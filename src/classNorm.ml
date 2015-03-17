(*
 * Copyright (c) 2014, TU Berlin
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 *   * Neither the name of the TU Berlin nor the
 *     names of its contributors may be used to endorse or promote products
 *     derived from this software without specific prior written permission.

 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL TU Berlin BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

(** Normalization of classLang expressions *)

module CamlFormat = Format
open Batteries
module Format = CamlFormat
                  
open Ast.Flags
open Syntax
open Class_deps
open Utils
open Location
open Motypes
open Report
       
exception ExpansionException of string
                                        
type prefix_found = { found : name ; not_found : name }

let show_prefix_found {found; not_found} = "No element named " ^ (name2str not_found) ^ " in " ^ (name2str found)
                      
type found_class = { found_value : Normalized.type_annotation ; found_visible : bool }

type found_replaceable = { fr_self : Normalized.object_struct ; fr_visible : bool ; fr_def : class_term ; fr_scope : scope ; fr_current : Normalized.type_annotation }
                     
type lookup_result = Found of found_class
                   | FoundReplaceable of found_replaceable
                   | NothingFound of name
                   | PrefixFound of prefix_found
                                      
type unresolved_dependency = { searching : name ; partial_result : prefix_found ; dependency : kontext_label }
                               
let fail_unresolved {searching; partial_result; dependency} = Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Dependency %s not evaluated:\n%s\n" (label2str dependency) (show_prefix_found partial_result)} ; fail
                               
exception DereferenceException of string

exception EvaluationException of string
exception UnresolvedDependency of unresolved_dependency
                                    
let result2str = function Found _ -> "OK"
               | PrefixFound pf -> show_prefix_found pf 
               | NothingFound name -> "No path to " ^ (name2str name)
                                                        
let unfolding = ref 0 

exception UnfoldingException

let rec filter_static = let open Normalized in function
    [] -> []
  | (k,SimpleType (Function f))::ts -> (k,Function f) :: (filter_static ts)
  | (k,Level2Type t)::ts when t.l2_variability = Constant -> (k,t.l2_type) :: (filter_static ts)
  | (k,v)::ts -> (filter_static ts)

let simplify =
  let open Normalized in
  (*TODO: location *)
  function
  | SimpleType cv -> return cv
  | UnknownType -> Report.do_ ; log {level=Error;where=none;what="Cannot resolve inheritance"} ; fail
  | Level2Type {l2_variability; l2_causality; l2_connectivity; l2_type} ->
     Report.do_ ;
     if_ (l2_variability != Constant) (log {level=Warning;where=none;what="Variability ignored in inheritance."});
     if_ (l2_causality != Acausal) (log {level=Warning;where=none;what="Causality ignored in inheritance."});
     if_ (l2_connectivity != Potential) (log {level=Warning;where=none;what="Connectivity ignored in inheritance."});
     return l2_type

let value_of = function
  | Found{found_value} -> return found_value
  | _ as f -> Report.do_ ; log{where=none;level=Error;what=result2str f}; fail
            
(* TODO: guard against circular evaluation/repeat until value *)
let rec unfold {Normalized.environment; expression; def_label} = Report.do_ ;
                                                                 v <-- eval environment expression ;
                                                                 return v                                                      
    
and eval_elements scope {fields} = Report.do_ ;
                                   (* only evaluate the fields, local and superclasses have been handled by the label-evaluation *)
                                   dynamic_fields <-- Report.on_strMap_values (eval scope) fields ;
                                   let static_fields = StrMap.of_list (filter_static (StrMap.bindings dynamic_fields)) in
                                   return {Normalized.class_members = StrMap.empty; super = []; dynamic_fields; static_fields}

and eval_flagged scope f flagged =
  Report.do_ ;
  v <-- eval scope flagged ;
  let open Normalized in
  begin
    match v with UnknownType -> return UnknownType
               | Level2Type l2 -> return (Level2Type (f l2))
               | SimpleType t -> 
                  return (Level2Type (f (default_level2 t)))
  end                                         
                                                                               
and eval scope = function
  | PClass {class_sort; public; protected} -> Report.do_ ;
                                              protected <-- eval_elements scope protected ;
                                              public <-- eval_elements scope public ;
                                              let open Normalized in
                                              return (SimpleType (Class {object_sort = class_sort ; public ; protected }))

  | Reference [] -> Report.do_ ;
                    log {where=none; level=Error ; what="Empty name found. Probably a bug."} ;
                    fail
  | Reference [{txt="StateSelect"}] -> return (Normalized.state_select_ta)

                      
  | PInt -> return (Normalized.SimpleType Int)
  | PReal -> return (Normalized.SimpleType Real)
  | PString -> return (Normalized.SimpleType String)
  | PBool -> return (Normalized.SimpleType Bool)
  | Reference (x::xs) -> Report.do_ ; f <-- start_lookup scope x xs ; value_of f
  | RootReference n -> Report.do_ ;
                       g <-- output ; 
                       f <-- get_class_element_st (Normalized.Class g) n ;
                       value_of f

  | PExternalObject -> return (Normalized.SimpleType ProtoExternalObject)

  | PArray {array_arg; dimensions} ->
     let open Normalized in
     let rec array_of_ta = function
             UnknownType -> UnknownType
           | SimpleType t -> SimpleType (Array {element= t; dimensions})
           | Level2Type l2 -> Level2Type {l2 with l2_type = Array {element = l2.l2_type; dimensions}}
           | Replaceable r -> Replaceable {r with current = array_of_ta r.current}
     in
     Report.do_ ; v <-- eval scope array_arg ;
     return (array_of_ta v)

  | PEnumeration es -> return (Normalized.SimpleType (Normalized.Enumeration es))

  | PCau {flag;flagged} -> eval_flagged scope (fun l2 -> {l2 with l2_causality = Normalized.cau_from_ast flag}) flagged
  | PCon {flag;flagged} -> eval_flagged scope (fun l2 -> {l2 with l2_connectivity = Normalized.con_from_ast flag}) flagged                            
  | PVar {flag;flagged} -> eval_flagged scope (fun l2 -> {l2 with l2_variability = Normalized.var_from_ast flag}) flagged

  | PSort {defined_sort=Connector; rhs} -> Report.do_ ;
                                           v <-- eval scope rhs ;
                                           let open Normalized in
                                           begin
                                             match v with
                                               SimpleType cv -> return (Level2Type {l2_type=cv; l2_variability=Continuous; l2_causality=Acausal; l2_connectivity=Potential})
                                             | Level2Type l2 -> return (Level2Type {l2 with l2_variability=Continuous})
                                             | UnknownType -> Report.do_ ; log{level=Warning; where=none; what="Unknown type"} ; return UnknownType
                                           end
                                             
  | PSort {defined_sort; rhs} -> Report.do_ ;
                                 v <-- eval scope rhs ;
                                 let open Normalized in
                                 begin
                                   match v with
                                   | SimpleType (Class {object_sort; public; protected}) when (defined_sort = object_sort) -> return v
                                   | SimpleType (Class {object_sort; public; protected}) ->
                                      Report.do_ ; log{level=Error; where=none; what=Printf.sprintf "Sort mismatch. This is not a %s but a %s" (show_sort defined_sort) (show_sort object_sort)}; fail
                                   | _ when defined_sort = Type -> return v
                                   | _ ->  Report.do_ ; log{level=Error; where=none; what=Printf.sprintf "Sort mismatch. This is not a %s but a type." (show_sort defined_sort)}; fail
                                 end
  | PReplaceable t -> Report.do_ ;
                      v <-- eval scope t ;
                      begin
                        let open Normalized in
                        match v with
                          UnknownType -> return UnknownType
                        | (SimpleType _ | Level2Type _) as current -> return (Replaceable {current; replaceable_body=t; replaceable_env=scope})
                      end             
  (* ignore empty redeclarations *)
  | StrictRedeclaration {rd_lhs; rds = []} -> eval scope rd_lhs
  | Redeclaration {rd_lhs; rds = []} -> eval scope rd_lhs
                                        
  | _ as e -> Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "'%s' not yet implemented" (show_class_term e)}; fail

and get_class_element_in {Normalized.class_members; super; static_fields; dynamic_fields} x xs =
  if StrMap.mem x.txt class_members then begin      
      Report.do_ ;
      r <-- (get_class_element (StrMap.find x.txt class_members) xs) ;
      match r with
        NothingFound name -> return (PrefixFound {not_found=name; found = [x]})
      | PrefixFound p -> return (PrefixFound {p with found = x::p.found})
      | r -> return r
    end
  else
    pickfirst_class (x::xs) super

and get_class_element e p =
  let open Normalized in 
  match e with
  | UnknownType -> Report.do_ ; log {level=Error;where=none;what=Printf.sprintf "Cannot resolve type '%s'" (name2str p)} ; fail
  | Level2Type _ as found_value when p = [] -> return (Found {found_value; found_visible=true})
  | Level2Type _ -> Report.do_ ; log {level=Error;where=none;what=Printf.sprintf "Cannot resolve type '%s' from a level-2 type." (name2str p)} ; fail 
  | SimpleType cv -> get_class_element_st cv p
                                                                                                                                     
and get_class_element_st e = function    
    [] -> return (Found {found_value = SimpleType e; found_visible=true})
  | x::xs -> begin
      match e with
      | Class ({protected;public} as fr_self) ->
         Report.do_ ;
         f <--  get_class_element_in public x xs ;
         begin
           match f with
             NothingFound _ -> get_class_element_in protected x xs
           | Found {found_value=Replaceable r; found_visible} -> return (FoundReplaceable {fr_self; fr_current=r.current; fr_visible=found_visible; fr_scope=r.replaceable_env; fr_def=r.replaceable_body})
           | _ as r -> return r
         end
      | Delayed d -> begin
         (* TODO: ensure termination, cache result? *)
         Report.do_ ;
         e' <-- unfold d ;
         get_class_element e' (x::xs)
        end
                       
      (* TODO: methods *)
      | _ -> return (NothingFound (x::xs))
    end    
               
and pickfirst_class name = function
    [] -> Report.return (NothingFound name)
  | v::vs ->
     Report.do_ ;
     f <-- get_class_element_st v name ;     
     begin match f with
             NothingFound _ -> pickfirst_class name vs
           | r -> return r
     end
                           
and lookup prefix suffix = function
    (* lookup scans through all possible source locations. We do not build the lexical environment from
       the currently evaluated pieces, but use the dependency analysis' "approximative environment" *)
    [] -> return (NothingFound (prefix::suffix))

  | ({source_label=(OutsideSuperclass {extended; parent})} as src) :: srcs ->
     (* handle the outside superclass like a normal superclass *)
     lookup prefix suffix ({src with source_label = Superclass (extended::parent)}::srcs)

  | {source_label=(Superclass p)} :: srcs ->
     begin
       Report.do_ ; e <-- output ; f <-- get_class_element_st (Class e) (List.rev p) ;
       match f with
       (* TODO: fix for short-hand extends *)
       | Found {found_value=Replaceable _} | FoundReplaceable _ -> Report.do_ ; log{level=Error;where=none;what="Cannot inherit replaceable class.\n"};fail

       | Found {found_value=(SimpleType st | Level2Type {l2_type=st}) ; found_visible} -> begin
           Report.do_ ; f' <-- get_class_element_st st (prefix::suffix) ;
           match f' with
           | NothingFound _ -> lookup prefix suffix srcs
           | PrefixFound pf -> return (PrefixFound pf)
           | Found f -> return (Found {f with found_visible = found_visible && f.found_visible})
         end
       | PrefixFound partial_result -> fail_unresolved { searching = prefix::suffix ; partial_result; dependency = Superclass p }
       | NothingFound not_found -> fail_unresolved { searching = prefix::suffix ; partial_result = {found=[]; not_found}; dependency = Superclass p }
     end

  | {source_label=Path(p)} :: _ ->
     begin
       Report.do_ ; e <-- output ; f <-- get_class_element_st (Class e) (List.rev p) ;
       match f with
       | Found {found_visible=false} -> Report.do_ ; log{level=Error;where=prefix.loc;what=Printf.sprintf "%s (= %s) is protected." prefix.txt (name2str p)} ; fail
       | Found {found_value} -> begin
           Report.do_ ; f' <-- get_class_element found_value suffix ;
           
           match f' with
             NothingFound _ -> return (PrefixFound { found = [prefix]; not_found = suffix })
           | PrefixFound {found; not_found} -> return (PrefixFound {found = prefix::found ; not_found})
           | r -> return r
         end
       | PrefixFound partial_result -> fail_unresolved { searching = prefix::suffix ; partial_result ; dependency = Path p }
       | NothingFound not_found -> fail_unresolved { searching = prefix::suffix ; partial_result = {found=[]; not_found}; dependency = Superclass p }
     end
                                    
and start_lookup scope prefix suffix =
  let sources = search_scope prefix [] scope in
  lookup prefix suffix sources

type class_ptr_element = PublicClass of string | ProtectedClass of string

let pp_class_ptr_element fmt = function
    PublicClass s -> Format.fprintf fmt "<public %s>" s                                    
  | ProtectedClass s -> Format.fprintf fmt "<protected %s>" s
                                       
type lexical_path = class_ptr_element Deque.t [@@deriving show]

type found_lexical = {lexical_path : lexical_path ; lexical_def : class_term }
                                      
let rec find_static_name lexical_def acc = function
    [] -> Some {lexical_path = acc; lexical_def}
  | x::r -> begin match lexical_def with
                    (* ignore redeclarations for static (aka lexical) lookup *)
                    (StrictRedeclaration {rd_lhs} | Redeclaration {rd_lhs}) -> find_static_name rd_lhs acc (x::r)
                                                                           
                    | PClass {public;protected} ->
                       begin
                         match StrMap.Exceptionless.find x.txt public.class_members  with
                           None -> begin
                             match StrMap.Exceptionless.find x.txt protected.class_members  with
                               None -> None
                             | Some e -> find_static_name e (Deque.snoc acc (ProtectedClass x.txt)) r
                           end
                         | Some e -> find_static_name e (Deque.snoc acc (PublicClass x.txt)) r
                       end
                         
                  | _ -> None
            end

type merge_tip = { tip_name : string ; tip_value : Normalized.type_annotation [@opaque]} [@@deriving show]
              
type merge_ptr = VoidTip
               | InsidePublic of merge_class
               | PublicTip of merge_tip
               | InsideProtected of merge_class
               | ProtectedTip of merge_tip
               | PublicSuperClass of Normalized.class_value
               | ProtectedSuperClass of Normalized.class_value [@@deriving show]

and merge_class = { class_name : string ; current_value : Normalized.object_struct [@opaque] ; next : merge_ptr } [@@deriving show]

let structure = let open Normalized in
                function    
                | SimpleType (Class os) -> return os
                | _ -> log{where=none;level=Error;what="Merge failed in non-structure"}; fail

let merge_classes cv_old cv_new =
  let open Normalized in 
  Report.do_ ;
  os' <-- structure cv_new ;
  os'' <-- structure cv_old ;
  return (SimpleType (Class {os'' with public = {os''.public with static_fields = os'.public.static_fields ; dynamic_fields = os'.public.dynamic_fields } ;
                                       protected = {os''.protected with static_fields = os'.protected.static_fields ; dynamic_fields = os'.protected.dynamic_fields }
                            }))
                                                                                           
let rec apply_merge (os:Normalized.object_struct) = function
  (* tips *)
  | VoidTip -> return os

  (* merge tips when already present *)
  | PublicTip {tip_name; tip_value} when StrMap.mem tip_name os.public.class_members ->
     Report.do_ ; cv <-- merge_classes (StrMap.find tip_name os.public.class_members) tip_value ;
     (* we only pick the dynamic/static fields, types are already present *)
     return {os with public = {os.public with class_members = StrMap.add tip_name cv os.public.class_members}}

  | ProtectedTip {tip_name; tip_value} when StrMap.mem tip_name os.protected.class_members ->
     Report.do_ ; cv <-- merge_classes (StrMap.find tip_name os.protected.class_members) tip_value ;
     (* we only pick the dynamic/static fields, types are already present *)
     return {os with protected = {os.protected with class_members = StrMap.add tip_name cv os.protected.class_members}}
            
  (* Direct overwrite every other tip *)
  | PublicTip {tip_name; tip_value} -> return {os with public = {os.public with class_members = StrMap.add tip_name tip_value os.public.class_members}}
  | ProtectedTip {tip_name; tip_value} -> return {os with protected = {os.protected with class_members = StrMap.add tip_name tip_value os.protected.class_members}}

  | PublicSuperClass s -> return {os with public = {os.public with super = s :: os.public.super}}
  | ProtectedSuperClass s -> return {os with public = {os.protected with super = s :: os.protected.super}}

  (* paths *)
  | InsidePublic {class_name; current_value; next} ->
     Report.do_ ;
     os' <-- apply_merge current_value next ;
     let cv = Normalized.SimpleType (Class os') in
     return {os with public = {os.public with class_members = StrMap.add class_name cv os.public.class_members}}

  | InsideProtected {class_name; current_value; next} ->
     Report.do_ ;
     os' <-- apply_merge current_value next ;
     let cv = Normalized.SimpleType (Class os') in
     return {os with protected = {os.protected with class_members = StrMap.add class_name cv os.protected.class_members}}
       
let rec lexical2merge tip cv p = match (Deque.front p) with
  | None -> return tip
  | Some (PublicClass class_name, ptr) ->  begin
      let open Normalized in
      match cv with

        SimpleType (Class os) ->
        let cv' = if StrMap.mem class_name os.public.class_members then StrMap.find class_name os.public.class_members else empty_class_ta in
        Report.do_ ;
        os <-- structure cv' ;
        next <-- lexical2merge tip cv' ptr ;
        return (InsidePublic {class_name; current_value = os; next})

      | SimpleType (Delayed dv) -> Report.do_ ; cv' <-- unfold dv ; lexical2merge tip cv' p
      | _ -> Report.do_ ; log{where=none;level=Error;what="Cannot merge non-class type with non-empty path " ^ class_name}; fail
    end
                                          
  | Some (ProtectedClass class_name, ptr) ->  begin
      let open Normalized in
      match cv with

        SimpleType (Class os) ->
        let cv' = if StrMap.mem class_name os.protected.class_members then StrMap.find class_name os.protected.class_members else empty_class_ta in
        Report.do_ ;
        os <-- structure cv' ;
        next <-- lexical2merge tip cv' ptr ;
        return (InsideProtected {class_name; current_value = os; next})

      | SimpleType (Delayed dv) -> Report.do_ ; cv' <-- unfold dv ; lexical2merge tip cv' p
      | _ -> Report.do_ ; log{where=none;level=Error;what="Cannot merge non-class type with non-empty path " ^ class_name}; fail
    end
                                                    
let add tip ptr =
  Report.do_ ;
  os <-- output ;
  mergePath <-- begin
      lexical2merge tip (SimpleType (Class os)) ptr
    end ;
  v <-- apply_merge os mergePath ;
  set_output v
             
let rec lexical_class_body = function
    (StrictRedeclaration {rd_lhs} | Redeclaration {rd_lhs}) -> lexical_class_body rd_lhs
  | PClass b -> return b
  | _ -> log{level=Error;where=none;what="Internal error. Got superclass but cannot find class body."};fail
             
let eval_label scope = function
    Path(x::p) ->
    begin
      Report.do_ ;
      c <-- input ;      
      let r = List.rev(x::p) in
      match find_static_name c Deque.empty r with
      (* we do not need to lookup dependencies of a static path, due to dependency analysis. 
         handle just the case where the hierarchy is empty *)
      | Some {lexical_path; lexical_def} ->
         Report.do_ ;
         (* if the body is a hierarchy, it is an empty one and we only have to add the name *)
         tip_value <-- eval scope lexical_def ;
         (rest,tip) <-- begin
             match Deque.rear lexical_path with Some (r, PublicClass tip_name) -> return (r, PublicTip {tip_name;tip_value})
                                              | Some (r, ProtectedClass tip_name) -> return (r, ProtectedTip {tip_name;tip_value})
                                              | None -> Report.do_ ; log{level=Error;where=none;what="Empty lexical path found. Error."};fail
           end ;
         add tip rest
             
      | _ -> Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Expansion of '%s' failed." (name2str r)}; fail
    end
      
  | Path([]) -> return () (* empty path, retain the current output *)
                 
  | OutsideSuperclass {extended; parent} ->
     (* the dependency analysis ensures that Σ.parent is already handled, so we can get the extended element
        from the globally evaluated environment. If this is a method, we need to force it. *)
     let r = List.rev (extended::parent) in
     begin
       Report.do_ ;
       c <-- input ;
       match find_static_name c Deque.empty r with
       | Some {lexical_path} -> begin
           Report.do_ ;
           global <-- output ;
           v <-- get_class_element_st (Class global) r ;
           
           match v with
             Found {found_value=SimpleType st; found_visible=true} -> add (PublicSuperClass st) lexical_path
           | Found (_) -> Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Illegal inheritance redeclaration of '%s' in %s" extended.txt (name2str parent)}; fail
           | _ -> Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Unknown superclass '%s' in %s" extended.txt (name2str parent)}; fail
         end
       | _ -> Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Expansion of '%s' failed." (name2str r)}; fail
     end
       
  | Superclass(p) ->
     Report.do_ ;
     c <-- input ;
     let r = List.rev p in
     
     begin match find_static_name c Deque.empty r with
             Some {lexical_path; lexical_def} ->
             Report.do_ ;             
             (* create an empty class just in case *)
             add VoidTip lexical_path ;                          
             {public;protected} <-- lexical_class_body lexical_def ;

             let eval_public_super v = Report.do_ ; 
                                       v <-- eval scope lexical_def ;
                                       s <-- simplify v;
                                       let tip = PublicSuperClass s in
                                       add tip lexical_path
             in

             let eval_protected_super v = Report.do_ ; 
                                          v <-- eval scope lexical_def ;
                                          s <-- simplify v ;
                                          let tip = ProtectedSuperClass s in
                                          add tip lexical_path
             in

             miter eval_public_super public.super ;
             miter eval_protected_super protected.super ;
             
           | _ -> Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Expansion of %s failed." (name2str r)}; fail
     end
                 
let step all count scopes kontext_label =
  BatLog.logf "[%d/%d] Normalizing %s\n" count all (label2str kontext_label) ;
  (*BatLog.logf "Context: %s\n" (cve2str v) ;*)
  let scope = LabelMap.find kontext_label scopes in
  eval_label scope kontext_label
        
exception SccNotSupportedException

let rec prepare_recursive scopes = function
  | [] -> return ()
  | (OutsideSuperclass _ | Superclass _ )::_ -> raise SccNotSupportedException
  | (Path []) :: _ -> raise SccNotSupportedException
  | Path(x::p)::r -> let q = List.rev(x::p) in
                     Report.do_ ;
                     c <-- input ;
                     log{level=Warning;where=none;what=Printf.sprintf "Handling possibly recursive element %s\n" (name2str (x::p))} ;
                     match find_static_name c Deque.empty q with
                     (* As for the non-recursive case, we only "evaluate" leafs of the definition tree *)
                     | Some {lexical_def=PClass h;lexical_path} -> (* everything inside, including the recursive occurrence, is covered by other labels *)
                        Report.do_; 
                        let tip_value = Normalized.empty_class_ta in
                        (ptr, tip) <-- begin match Deque.rear lexical_path with Some (ptr, PublicClass tip_name) -> return (ptr, PublicTip {tip_name;tip_value})
                                                                              | Some (ptr, ProtectedClass tip_name) -> return (ptr, ProtectedTip {tip_name;tip_value})
                                                                              | None -> Report.do_ ; log{level=Error;where=none;what="Empty lexical path found. Error."};fail
                                                                                                                                                                           
                                       end;             
                        add tip ptr ;
                        prepare_recursive scopes r
                                          
                     (* Only add a recursive entry for the leafs *)
                     | Some {lexical_def;lexical_path} ->
                        Report.do_;
                        log{level=Warning;where=none;what=Printf.sprintf "Adding recursive entry for %s\n" (name2str (x::p))} ;
                        let tip_value = Normalized.SimpleType (Normalized.Delayed {environment = LabelMap.find (Path p) scopes; expression = lexical_def; def_label=x::p}) in
                        (ptr, tip) <-- begin match Deque.rear lexical_path with Some (ptr, PublicClass tip_name) -> return (ptr, PublicTip {tip_name;tip_value})
                                                                              | Some (ptr, ProtectedClass tip_name) -> return (ptr, ProtectedTip {tip_name;tip_value})
                                                                              | None -> Report.do_ ; log{level=Error;where=none;what="Empty lexical path found. Error."};fail
                                                                                                                                                                           
                                       end;             
                        add tip ptr ;
                        prepare_recursive scopes r
                                          
                     | _ -> Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Expansion of '%s' failed." (name2str q)}; fail
                                                          

let rec do_normalize all count scopes r = function
    [] -> begin match r with
                  [] -> return ()
                | [l]::r -> (* singleton scc *)
                   do_normalize all count scopes r [l]
                | x::r ->
                   (* handle a recursive scc *)
                   BatLog.logf "Preparing a recursive group with %d entries\n" (List.length x) ;
                   Report.do_ ;
                   prepare_recursive scopes x ;
                   do_normalize all count scopes r x
          end
  | x::xs ->
     (* either singletons or prepared recursives *)
     Report.do_ ;
     step all (count+1) scopes x ;     
     do_normalize all (count + 1) scopes r xs

let name = function
    Short tds -> tds.td_name | Composition tds -> tds.td_name | Enumeration tds -> tds.td_name | OpenEnumeration tds -> tds.td_name | DerSpec tds -> tds.td_name | Extension tds -> tds.td_name
                  
let global_scope start = List.map (fun td -> {scope_name=[];scope_tainted=false;scope_entries=StrMap.singleton ((name td.commented).txt) (name td.commented)}) start

let normalize top = 
  BatLog.logf "Starting class-language normalization.\n" ;
  let deps = scan_dependencies (global_scope top) top in
  let scopes = List.fold_left (fun m {kontext_label;scope} -> LabelMap.add kontext_label scope m) LabelMap.empty deps in
  let sccs = topological_order deps in
  let length = List.fold_left (fun s l -> s + (List.length l)) 0 sccs in
  let state = {messages = []; input = ClassTrans.translate_topdefs top; output = Normalized.empty_class_body} in    
  let o = Report.run (Report.do_ ; do_normalize length 0 scopes sccs [] ; output) state in
  BatLog.logf "Finished class-language normalization.\n" ;
  o
