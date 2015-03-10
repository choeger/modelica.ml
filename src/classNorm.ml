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

type found_class = { found_value : Normalized.class_value ; found_visible : bool }
                      
type lookup_result = Found of found_class
                   | NothingFound of name
                   | PrefixFound of prefix_found

type unresolved_dependency = { searching : name ; dependency : kontext_label }

let fail_unresolved {searching; dependency} = Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Dependency %s not evaluated\n" (label2str dependency)} ; fail
                               
exception DereferenceException of string

exception EvaluationException of string
exception UnresolvedDependency of unresolved_dependency
                                    
let result2str = function Found _ -> "OK"
               | PrefixFound {found; not_found} -> "No element named " ^ (name2str not_found) ^ " in " ^ (name2str found)
               | NothingFound name -> "No path to " ^ (name2str name)
                                                        
let value_of = function Found(v) -> v | r -> raise (EvaluationException (result2str r))

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
                   
(* TODO: guard against circular evaluation/repeat until value *)
let rec unfold {Normalized.environment; expression; def_label} = Report.do_ ;
                                                                 v <-- eval environment expression ;
                                                                 return v                                                      
    
and eval_elements scope {fields} = Report.do_ ;
                                   (* only evaluate the fields, local and superclasses have been handled by the label-evaluation *)
                                   dynamic_fields <-- Report.on_strMap_values (eval scope) fields ;
                                   let static_fields = StrMap.of_list (filter_static (StrMap.bindings dynamic_fields)) in
                                   return {Normalized.class_members = StrMap.empty; super = []; dynamic_fields; static_fields}
and eval scope = function
  | PClass {class_sort; public; protected} -> Report.do_ ;
                                              protected <-- eval_elements scope protected ;
                                              public <-- eval_elements scope public ;
                                              let open Normalized in
                                              return (SimpleType (Class {object_sort = class_sort ; public ; protected }))

  | Reference [] -> Report.do_ ;
                    log {where=none; level=Error ; what="Empty name found. Probably a bug."} ;
                    fail
  (*                    
  | Reference (x::xs) -> value_of(start_lookup v scope x xs)
  | RootReference n -> value_of (get_element v {vkind=Static;vbody=VHierarchy v} n)
  | PInt -> SimpleType Int
  | PReal -> SimpleType Real
  | PString -> SimpleType String
  | PBool -> SimpleType Bool
  | PExternalObject -> SimpleType ProtoExternalObject
  | PArray {array_arg; dimensions} -> begin match eval v scope array_arg with
                                        UnknownType -> UnknownType
                                      | SimpleType t -> SimpleType (Array {element= t; dimensions})
                                      | Level2Type l2 -> Level2Type {l2 with l2_type = Array {element = l2.l2_type; dimensions}}
                                      end
  | PEnumeration ls -> SimpleType (Enumeration ls)
   *)                                 

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

and get_class_element e p = match e with
  | UnknownType -> Report.do_ ; log {level=Error;where=none;what=Printf.sprintf "Cannot resolve type '%s'" (name2str p)} ; fail 
  | Level2Type _ -> Report.do_ ; log {level=Error;where=none;what=Printf.sprintf "Cannot resolve type '%s' from a level-2 type." (name2str p)} ; fail 
  | SimpleType cv -> get_class_element_st cv p
                                                                                                                                     
and get_class_element_st e = function    
    [] -> return (Found {found_value = e; found_visible=true})
  | x::xs -> begin
      match e with
      | Class {protected;public} ->
         Report.do_ ;
         f <--  get_class_element_in public x xs ;
         begin
           match f with
             NothingFound _ -> get_class_element_in protected x xs
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
       | Found {found_value;found_visible} -> begin
           Report.do_ ; f' <-- get_class_element_st found_value (prefix::suffix) ;
           match f' with
           | NothingFound _ -> lookup prefix suffix srcs
           | PrefixFound pf -> return (PrefixFound pf)
           | Found f -> return (Found {f with found_visible = found_visible && f.found_visible})
         end
       | _ -> fail_unresolved { searching = prefix::suffix ; dependency = Superclass p }
     end

  | {source_label=Path(p)} :: _ ->
     begin
       Report.do_ ; e <-- output ; f <-- get_class_element_st (Class e) (List.rev p) ;
       match f with
       | Found {found_visible=false} -> Report.do_ ; log{level=Error;where=prefix.loc;what=Printf.sprintf "%s (= %s) is protected." prefix.txt (name2str p)} ; fail
       | Found {found_value} -> begin
           Report.do_ ; f' <-- get_class_element_st found_value suffix ;
           
           match f' with
             NothingFound _ -> return (PrefixFound { found = [prefix]; not_found = suffix })
           | PrefixFound {found; not_found} -> return (PrefixFound {found = prefix::found ; not_found})
           | r -> return r
         end
       | _ -> fail_unresolved { searching = prefix::suffix ; dependency = Superclass p }
     end
                                    
and start_lookup scope prefix suffix =
  let sources = search_scope prefix [] scope in
  lookup prefix suffix sources

type class_ptr_element = PublicClass of string | ProtectedClass of string

type lexical_path = class_ptr_element list

type found_lexical = {lexical_path : lexical_path ; lexical_def : class_term }
                                      
let rec find_static_name lexical_def lexical_path = function
    [] -> Some {lexical_path; lexical_def}
  | x::r -> begin match lexical_def with
                    (* ignore redeclarations for static (aka lexical) lookup *)
                    (StrictRedeclaration {rd_lhs} | Redeclaration {rd_lhs}) -> find_static_name rd_lhs lexical_path (x::r)
                                                                           
                    | PClass {public;protected} ->
                       begin
                         match StrMap.Exceptionless.find x.txt public.class_members  with
                           None -> begin
                             match StrMap.Exceptionless.find x.txt protected.class_members  with
                               None -> None
                             | Some e -> find_static_name e ((PublicClass x.txt)::lexical_path) r
                           end
                         | Some e -> find_static_name e ((PublicClass x.txt)::lexical_path) r
                       end
                         
                  | _ -> None
            end

type merge_tip = { tip_name : string ; tip_value : Normalized.type_annotation }
              
type merge_ptr = InsidePublic of merge_class
               | PublicTip of merge_tip
               | InsideProtected of merge_class
               | ProtectedTip of merge_tip
               | PublicSuperClass of Normalized.class_value
               | ProtectedSuperClass of Normalized.class_value

and merge_class = { class_name : string ; current_value : Normalized.object_struct ; next : merge_ptr }

let rec apply_merge (os:Normalized.object_struct) = function
  (* tips *)
  | PublicTip {tip_name; tip_value} -> {os with Normalized.public = {os.public with Normalized.class_members = StrMap.add tip_name tip_value os.public.class_members}}
  | ProtectedTip {tip_name; tip_value} -> {os with protected = {os.protected with class_members = StrMap.add tip_name tip_value os.protected.class_members}}
  | PublicSuperClass s ->  {os with public = {os.public with super = s :: os.public.super}}
  | ProtectedSuperClass s ->  {os with public = {os.protected with super = s :: os.protected.super}}

  (* paths *)
  | InsidePublic {class_name; current_value; next} -> let cv = Normalized.SimpleType (Class (apply_merge current_value next)) in
                                                      {current_value with public = {current_value.public with class_members = StrMap.add class_name  cv current_value.public.class_members}}
  | InsideProtected {class_name; current_value; next} -> let cv = Normalized.SimpleType (Class (apply_merge current_value next)) in
                                                         {current_value with protected = {current_value.protected with class_members = StrMap.add class_name cv current_value.protected.class_members}}


let rec lexical2merge tip cv = function
  | [] -> return tip
  | (PublicClass class_name) :: ptr ->  begin
      let open Normalized in
      match cv with

        SimpleType (Class os) ->
        let cv' = if StrMap.mem class_name os.public.class_members then StrMap.find class_name os.public.class_members else empty_class_ta in
        Report.do_ ;
        next <-- lexical2merge tip cv' ptr ;
        return (InsidePublic {class_name; current_value = os; next})

      | SimpleType (Delayed dv) -> Report.do_ ; cv' <-- unfold dv ; lexical2merge tip cv' ((PublicClass class_name) :: ptr)
      | _ -> Report.do_ ; log{where=none;level=Error;what="Cannot merge non-class type with non-empty path " ^ class_name}; fail
    end
                                          
  | (ProtectedClass class_name) :: ptr ->  begin
      let open Normalized in
      match cv with

        SimpleType (Class os) ->
        let cv' = if StrMap.mem class_name os.protected.class_members then StrMap.find class_name os.protected.class_members else empty_class_ta in
        Report.do_ ;
        next <-- lexical2merge tip cv' ptr ;
        return (InsideProtected {class_name; current_value = os; next})

      | SimpleType (Delayed dv) -> Report.do_ ; cv' <-- unfold dv ; lexical2merge tip cv' ((ProtectedClass class_name) :: ptr)
      | _ -> Report.do_ ; log{where=none;level=Error;what="Cannot merge non-class type with non-empty path " ^ class_name}; fail
    end
                                                    
let add tip ptr =
  Report.do_ ;
  os <-- output ;
  mergePath <-- lexical2merge tip (SimpleType (Class os)) ptr ;
  set_output (apply_merge os mergePath)

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
      match find_static_name c [] r with
      (* we do not need to lookup dependencies of a static path, due to dependency analysis. 
         handle just the case where the hierarchy is empty *)
      | Some {lexical_path=hd::ptr; lexical_def} ->
         Report.do_ ;
         (* if the body is a hierarchy, it is an empty one and we only have to add the name *)
         tip_value <-- eval scope lexical_def ;
         let tip = match hd with PublicClass tip_name -> PublicTip {tip_name;tip_value} | ProtectedClass tip_name -> ProtectedTip {tip_name;tip_value} in             
         add tip ptr
             
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
       match find_static_name c [] r with
       | Some {lexical_path} -> begin
           Report.do_ ;
           global <-- output ;
           v <-- get_class_element_st (Class global) r ;
           
           match v with
             Found {found_value; found_visible} -> add (PublicSuperClass found_value) lexical_path
           | Found (_) -> Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Illegal inheritance redeclaration of '%s' in %s" extended.txt (name2str parent)}; fail
           | _ -> Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Unknown superclass '%s' in %s" extended.txt (name2str parent)}; fail
         end
       | _ -> Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Expansion of '%s' failed." (name2str r)}; fail
     end
       
  | Superclass(p) ->
     Report.do_ ;
     c <-- input ;
     let r = List.rev p in
     
     begin match find_static_name c [] r with
             Some {lexical_path; lexical_def} ->
             Report.do_ ;
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

             on_unit_sequence eval_public_super public.super ;
             on_unit_sequence eval_protected_super protected.super ;
             
           | _ -> Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Expansion of %s failed." (name2str r)}; fail
     end
                 
let step all count scopes kontext_label =
  BatLog.logf "[%d/%d] Normalizing %s\n" count all (label2str kontext_label) ;
  (*BatLog.logf "Context: %s\n" (cve2str v) ;*)
  let scope = LabelMap.find kontext_label scopes in
  eval_label scope kontext_label
        
exception SccNotSupportedException

let rec prepare_recursive c scopes v = function
  | [] -> v
  | (OutsideSuperclass _ | Superclass _ )::_ -> raise SccNotSupportedException
  | (Path []) :: _ -> raise SccNotSupportedException
  | Path(x::p)::r -> let q = List.rev(x::p) in                                          
                     BatLog.logf "Handling possibly recursive element %s\n" (name2str (x::p)) ;
                     match find_static_name c q with
                       None -> raise (ExpansionException (name2str q))
                     (* As for the non-recursive case, we only "evaluate" leafs of the definition tree *)
                     | Some {body=Hierarchy h} -> (* everything inside is covered by other labels *) prepare_recursive c scopes (add v empty_hierarchy (x::p)) r
                     (* Only add a recursive entry for the leafs *)
                     | Some {kind;body} -> let vbody = VDelayed {environment = LabelMap.find (Path p) scopes; expression = body; def_label=x::p} in
                                           BatLog.logf "Adding recursive entry for %s\n" (name2str (x::p)) ;
                                           let v' = add v {vfields = StrMap.singleton x.txt {vkind=kind;vbody}; vsuper=[]} p in
                                           prepare_recursive c scopes v' r
                                                          

let rec do_normalize all count c scopes v r = function
    [] -> begin match r with
                  [] -> v
                | [l]::r -> do_normalize all count c scopes v r [l]
                | x::r ->
                   let v' = prepare_recursive c scopes v x in
                   do_normalize all count c scopes v' r x
          end
  | x::xs ->
     let v' = (step all (count+1) c scopes v x) in
     do_normalize all (count + 1) c scopes v' r xs

let name = function
    Short tds -> tds.td_name | Composition tds -> tds.td_name | Enumeration tds -> tds.td_name | OpenEnumeration tds -> tds.td_name | DerSpec tds -> tds.td_name | Extension tds -> tds.td_name
                  
let global_scope start = [{scope_name=[];scope_tainted=false;scope_entries=StrMap.singleton start.txt start}]

let log_source {source_label; required_elements} = BatLog.logf "    %s, leaving: %s\n" (label2str source_label) (name2str required_elements) 
                           
let log_dep {local_name;from} = BatLog.logf "  '%s' might be defined in:\n" local_name; List.iter log_source from

let log_def {kontext_label; dependencies} = BatLog.logf "Dependencies for %s:\n" (label2str kontext_label) ; List.iter log_dep dependencies 
                           
let normalize top = 
    let deps = scan_dependencies (global_scope (name top.commented)) top in
    let scopes = List.fold_left (fun m {kontext_label;scope} -> LabelMap.add kontext_label scope m) LabelMap.empty deps in
    let sccs = topological_order deps in
    let length = List.fold_left (fun s l -> s + (List.length l)) 0 sccs in
    do_normalize length 0 ({body=translate_topdefs [top];kind=Static}) scopes empty_hierarchy sccs []
