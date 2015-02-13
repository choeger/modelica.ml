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

module CamlFormat = Format
open Batteries
open Syntax
open Class_deps
open Utils
open Location
       
type class_ = Hierarchy of hierarchy
            | Reference of name
            | RootReference of name
            | Primitive of string * (class_ list)
            | Method of string list

 and hierarchy = { fields : class_element StrMap.t ; super : class_ list }
                               
 and class_element = { kind : class_element_kind ; body : class_ }

 and class_element_kind = Static
                        | Replaceable
                        | Function

type t = class_

type class_value = VHierarchy of value_hierarchy
                 | VPrimitive of string * class_value list
                 | VMethod of string list
                 | VDelayed of delayed_value

 and delayed_value = { environment : scope ; expression : class_ }
                                 
 and value_hierarchy = { vfields : class_value_element StrMap.t ; vsuper : class_value list }
                               
 and class_value_element = { vkind : class_element_kind ; vbody : class_value }

let empty_hierarchy = {vfields=StrMap.empty ; vsuper = []}

open CamlFormat

let pp_comma fmt () = fprintf fmt ", "
       
let rec pp_cv fmt = function
  | VDelayed _ -> fprintf fmt "<delayed>"
  | VHierarchy vh -> pp_hierarchy fmt vh
  | VPrimitive (x, cs) -> fprintf fmt "@[%s(%a)@]" x (pp_print_list ~pp_sep:pp_comma pp_cv) cs

and pp_cv_element fmt {vkind;vbody} = fprintf fmt "%s%a" (match vkind with Function -> "function " | Replaceable -> "replaceable " | _ -> "") pp_cv vbody
                                  
and pp_field fmt (x, e) = fprintf fmt "%s = %a" x pp_cv_element e
                                  
and pp_hierarchy fmt {vfields;vsuper} = fprintf fmt "{%a; extends %a}"
                                                (pp_print_list ~pp_sep:pp_comma pp_field) (StrMap.bindings vfields)
                                                (pp_print_list ~pp_sep:pp_comma pp_cv) vsuper
                                            

let cv2str  ?max:(n=8) cv = 
  pp_set_max_boxes str_formatter n ;
  (pp_cv str_formatter cv) ;
  flush_str_formatter ()

let cve2str  ?max:(n=8) cve = 
  pp_set_max_boxes str_formatter n ;
  (pp_cv_element str_formatter cve) ;
  flush_str_formatter ()

let hier2str ?max:(n=8) cve = 
  pp_set_max_boxes str_formatter n ;
  (pp_hierarchy str_formatter cve) ;
  flush_str_formatter ()

                      
                      
let kindof e = function
    Syntax.Function | OperatorFunction -> { kind = Function ; body = e }
    | _ -> { kind = Static; body = e}
             
let rec translate_tds = function
  | Short tds -> (tds.td_name.txt,kindof (translate_texp tds.type_exp) tds.sort)
                               
  | Composition tds -> (tds.td_name.txt, kindof (Hierarchy (translate_comp tds.type_exp)) tds.sort)
                            
  | Enumeration tds -> (tds.td_name.txt,kindof (Primitive ("enumeration", [])) tds.sort) 
  | OpenEnumeration tds -> (tds.td_name.txt,kindof (Primitive ("open enumeration", [])) tds.sort)
  | DerSpec tds -> (tds.td_name.txt,kindof (Primitive ("derivative", [])) tds.sort)
  | Extension tds ->
     let comp,mo = tds.type_exp in
     let h = translate_comp comp in
     let f = match mo with Some m -> translate_redeclarations m | None -> StrMap.empty in
     (tds.td_name.txt, kindof (Hierarchy {h with fields = StrMap.union h.fields f}) tds.sort)

and translate_topdefs tds = Hierarchy {fields = StrMap.of_enum (Enum.map translate_typedef (List.enum tds)); super=[]}
                                   
and translate_typedef td = translate_tds td.commented
                                   
and translate_extends {ext_type} = translate_texp ext_type
                                   
and translate_elements {extensions;typedefs;redeclared_types} = 
  let super = List.map translate_extends extensions in
  let own_fields = Enum.map translate_typedef (List.enum typedefs) in
  let overloaded = Enum.map translate_typedef (List.enum redeclared_types) in
  {fields = StrMap.of_enum (Enum.concat (List.enum [own_fields;overloaded])) ; super}
  
and translate_comp { public ; protected; } =
  let public = translate_elements public in
  let protected = translate_elements protected in
  {fields = StrMap.union public.fields protected.fields ; super = public.super @ protected.super}

and translate_redeclarations {types} =
  StrMap.of_enum (Enum.map (fun trd -> translate_tds (Short trd.redecl_type.commented)) (List.enum types))
    
and translate_texp = function
  | TName n -> Reference n
  | TRootName n -> RootReference n
                                 
  | TArray {base_type} -> Primitive("Array", [translate_texp base_type])
  | TMod {mod_type; modification} -> Hierarchy {super=[translate_texp mod_type]; fields = translate_redeclarations modification}
  | TVar {flagged} -> Primitive ("Variability", [translate_texp flagged] )
  | TCon {flagged} -> Primitive ("Connectivity", [translate_texp flagged] )
  | TCau {flagged} -> Primitive ("Causality", [translate_texp flagged] )

exception ExpansionException of string
            
let rec find_static_name e = function
    [] -> Some e               
  | x::r -> begin match e.body with
                    Hierarchy {fields} ->
                    begin
                      match StrMap.Exceptionless.find x.txt fields with
                        None -> None
                      | Some e -> find_static_name e r
                    end
                  | _ -> None
            end
      
type prefix_found = { found : name ; not_found : name }
                           
type lookup_result = Found of class_value_element
                   | NothingFound of name
                   | PrefixFound of prefix_found

type unresolved_dependency = { searching : name ; dependency : kontext_label }
                                      
exception DereferenceException of string

exception EvaluationException of string
exception UnresolvedDependency of unresolved_dependency
                                    
let result2str = function Found _ -> "OK"
               | PrefixFound {found; not_found} -> "No element named " ^ (name2str not_found) ^ " in " ^ (name2str found)
               | NothingFound name -> "No path to " ^ (name2str name)
                                                        
let value_of = function Found(e) -> e.vbody | r -> raise (EvaluationException (result2str r))
                                    
let rec unfold global {environment; expression} = eval global environment expression
                                             
and eval v scope = function
  | Hierarchy {fields;super} -> VHierarchy {vfields = StrMap.map (eval_element v scope) fields; vsuper = List.map (eval v scope) super}
  | Reference [] -> raise Syntax_fragments.EmptyName                          
  | Reference [x] when builtin x.txt -> VPrimitive (x.txt, [])
  | Reference (x::xs) -> value_of(start_lookup v scope x xs)
  | RootReference n -> value_of (get_element v {vkind=Static;vbody=VHierarchy v} n)
  | Primitive (s, cs) -> VPrimitive (s, List.map (eval v scope) cs)
(*| Method of string list*)

and get_element global e = function    
    [] -> Found e            
  | x::xs -> begin
      match e.vbody with
      | VHierarchy {vfields;vsuper} ->
         if StrMap.mem x.txt vfields then
           match get_element global (StrMap.find x.txt vfields) xs with
             NothingFound name -> PrefixFound {not_found=name; found = [x]}
           | PrefixFound p -> PrefixFound {p with found = x::p.found}
           | r -> r
         else
           pickfirst global (x::xs) vsuper
      | VDelayed d ->
      (* TODO: ensure termination, cache result? *) get_element global {e with vbody=unfold global d} (x::xs)
         
      (* TODO: methods *)
      | _ -> NothingFound (x::xs)
    end    
               
and pickfirst global name = function
    [] -> NothingFound name
  | v::vs -> begin match get_element global {vkind = Static ; vbody = v} name with
                     NothingFound _ -> pickfirst global name vs
                   | _ as r -> r
             end
                           
and lookup global e prefix suffix = function
    [] -> NothingFound (prefix::suffix)
  | ({source_label=(OutsideSuperclass {extended; parent})} as src) :: srcs ->
     (* handle the outside superclass like a normal superclass *)
     lookup global e prefix suffix ({src with source_label = Superclass (extended::parent)}::srcs)
  | {source_label=(Superclass p)} :: srcs ->
     begin
       match get_element global e (List.rev p) with
       | Found e' -> begin
           match get_element global e' (prefix::suffix) with
           | NothingFound _ -> lookup global e prefix suffix srcs
           | r -> r
         end
         | _ -> raise (UnresolvedDependency { searching = prefix::suffix ; dependency = Superclass p })
     end
  | {source_label=Path(p)} :: _ ->
     begin
       match get_element global e (List.rev p) with
       | Found e' -> begin 
           (*BatLog.logf "Looking for %s in scope %s\n" (name2str suffix) (name2str p) ;*)
           match get_element global e' suffix with NothingFound _ -> PrefixFound { found = [prefix]; not_found = suffix }
                                                 | r -> r
         end
       | _ -> raise (UnresolvedDependency { searching = prefix::suffix ; dependency = Path p })
     end
                                    
and start_lookup global scope prefix suffix =
  let sources = search_scope prefix [] scope in
  lookup global {vkind=Static;vbody=VHierarchy global} prefix suffix sources
                                    
and eval_element global scope {kind; body} = {vkind=kind; vbody=eval global scope body}
                                               
let rec merge_kind a = function
    Static -> a
  | b -> b
            
let rec merge_elements global b = function
    {vbody=VHierarchy ha; vkind=ka} as a -> begin match b with {vbody=VHierarchy hb; vkind=kb} -> {vbody=VHierarchy (merge global ha hb); vkind=merge_kind kb ka}
                                                             | {vbody=VDelayed delayed; vkind=kb} -> merge_elements global {vbody=unfold global delayed; vkind=kb} a
                                                             | _ -> raise (DereferenceException ("Cannot merge non-hierarchy " ^ (cve2str b)))
                                            end
  | {vbody=VDelayed d; vkind} -> merge_elements global b {vbody=unfold global d; vkind}
  | a -> raise (DereferenceException ("Cannot merge non-hierarchy " ^ (cve2str b) ^ " with lhs " ^ (cve2str a)))
               
               
and merge global ha hb = 
  let merge_add fds (x,cve) = if StrMap.mem x fds then StrMap.modify x (merge_elements global cve) fds else StrMap.add x cve fds in
  let vfields = List.fold_left merge_add ha.vfields (StrMap.bindings hb.vfields) in
  let vsuper = ha.vsuper @ hb.vsuper in
  {vfields; vsuper}
            
and merge_hier global root a = function
    [] -> merge global root a 
  | x::r -> merge_hier global root {vfields=StrMap.singleton x.txt {vbody=VHierarchy a;vkind=Static} ; vsuper=[]} r
                       
let add global e p = merge_hier global global e p

let add_superclasses global vsuper p = merge_hier global global {empty_hierarchy with vsuper} p
                                                  
let eval_label c scope global = function    
    Path(x::p) ->
    begin
     let r = List.rev(x::p) in
     match find_static_name c (r) with
     (* we do not need to lookup dependencies of a static path, due to dependency analysis. 
        handle just the case where the hierarchy is empty *)
     | Some {body=Hierarchy {fields;super=[]}} when not (StrMap.is_empty fields)-> (* everything covered by earlier labels *) global
     | Some {kind;body} ->
        (* if the body is a hierarchy, it is an empty one and we only have to add the name *)
        let vbody = match body with Hierarchy _ -> VHierarchy empty_hierarchy | _ -> eval global scope body in
        add global {vfields = StrMap.singleton x.txt {vkind=kind;vbody}; vsuper=[]} p
     | None -> raise (ExpansionException (name2str (List.rev p)))
    end
  | Path(_) -> global
  | OutsideSuperclass {extended; parent} ->
     (* the dependency analysis ensures that Σ.parent is already handled, so we can get the extended element
        from the globally evaluated environment. If this is a method, we need to force it. *)
     let r = List.rev (extended::parent) in
     begin
       match get_element global {vkind=Static; vbody=VHierarchy global} r with
         Found {vbody=(VHierarchy h) as v} -> BatLog.logf "Adding superclass %s to %s\n" (cv2str v) (name2str r) ; add_superclasses global [v] (extended::parent)
       | Found (_) -> raise (EvaluationException (Printf.sprintf "Illegal inheritance redeclaration of '%s' in %s" extended.txt (name2str parent)))
       | _ -> raise (EvaluationException (Printf.sprintf "Unknown superclass '%s' in %s" extended.txt (name2str parent)))
     end                                                    
  | Superclass(p) ->
     begin match find_static_name c (List.rev p) with
             Some {kind;body=Hierarchy h} ->
             add_superclasses global (List.map (eval global scope) h.super) p
           | _ -> raise (ExpansionException (name2str p))
     end
                 
let step all count c scopes v kontext_label =
  BatLog.logf "[%d/%d] Normalizing %s\n" count all (label2str kontext_label) ;
  (*BatLog.logf "Context: %s\n" (cve2str v) ;*)
  let scope = LabelMap.find kontext_label scopes in
  try 
    eval_label c scope v kontext_label
  with UnresolvedDependency {searching; dependency} as err -> BatLog.fatalf "Dependency %s not evaluated\n" (label2str dependency) ; raise err
     | (EvaluationException err) as e -> let bt = Printexc.get_backtrace () in BatLog.logf "Error: %s\n" err ; BatLog.fatal bt 
        
exception SccNotSupportedException

let rec step_recursive c scopes v = function
  | [] -> v
  | (OutsideSuperclass _ | Superclass _ )::_ -> raise SccNotSupportedException
  | (Path []) :: _ -> raise SccNotSupportedException
  | Path(x::p)::r -> let q = List.rev(x::p) in
                     match find_static_name c q with
                       None -> raise (ExpansionException (name2str q))
                     | Some {kind;body} -> let vbody = VDelayed {environment = LabelMap.find (Path p) scopes; expression = body} in
                                           let v' = add v {vfields = StrMap.singleton x.txt {vkind=kind;vbody}; vsuper=[]} p in
                                           step_recursive c scopes v' r
                                                          
            
let rec do_normalize all count c scopes v = function
    [] -> v
  | [l]::r -> do_normalize all (count + 1) c scopes (step all (count+1) c scopes v l) r
  | x::r -> do_normalize all (count + 1) c scopes (step_recursive c scopes v x) r

let name = function
    Short tds -> tds.td_name | Composition tds -> tds.td_name | Enumeration tds -> tds.td_name | OpenEnumeration tds -> tds.td_name | DerSpec tds -> tds.td_name | Extension tds -> tds.td_name
                  
let global_scope start = [{scope_name=[];scope_tainted=false;scope_entries=StrMap.singleton start.txt start}]

let log_source {source_label; required_elements} = BatLog.logf "    %s, leaving: %s\n" (label2str source_label) (name2str required_elements) 
                           
let log_dep {local_name;from} = BatLog.logf "  '%s' might be defined in:\n" local_name; List.iter log_source from

let log_def {kontext_label; dependencies} = BatLog.logf "Dependencies for %s:\n" (label2str kontext_label) ; List.iter log_dep dependencies 
                           
let normalize top = 
    let deps = scan_dependencies (global_scope (name top.commented)) top in
    List.iter log_def deps ;
    let scopes = List.fold_left (fun m {kontext_label;scope} -> LabelMap.add kontext_label scope m) LabelMap.empty deps in
    let sccs = topological_order deps in
    do_normalize (List.length sccs) 0 ({body=translate_topdefs [top];kind=Static}) scopes empty_hierarchy sccs
