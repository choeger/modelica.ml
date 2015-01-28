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

open Batteries
open Utils
open Syntax
open Traversal
       
type kontext_label = Path of string list
                   | Superclass of string list

type dependency = {
  local_name : string;
  from : kontext_label list;
  element : string list;
}

type lexical_typedef = {
  kontext_label : kontext_label;
  dependencies : dependency list;
}

type scope_entry = {
  scope_name : string list ;
  scope_tainted: bool;
  scope_entries :  StrSet.t;
}

type scope = scope_entry list
                                  

(** Find all possible global names of a given identifier in the given scope *)
let rec find x = function
    (* when x is in the scope, tainted does not matter, it shadows all entries above *)
    {scope_entries; scope_name}::rest when StrSet.mem x scope_entries -> [Path (x::scope_name)]
  (* when the scope is not tainted, use "normal" lexical scoping *)
  | {scope_tainted=false}::rest -> find x rest
  (* when the scope is tainted, we have to consider it *)
  | {scope_tainted=true; scope_name}::rest -> (Superclass (scope_name))::(find x rest)
  | [] -> []
                         
type scanner_result = {
  found : lexical_typedef list;
  scope : scope;
}

let builtin = function
  | "String" | "Real" | "Boolean" | "Integer" -> true
  | _ -> false
                        
(** Compute a dependency from a type-expression *)
let rec dependency es scope = function
  | TIde x when builtin x -> None
  | TIde x -> let from = find x scope in Some {local_name = x ; from ; element=es}
  | TRootide x -> Some {from = [Path(x :: es)] ; local_name=x ; element = []}
  | TProj {class_type; type_element} -> dependency (type_element::es) scope class_type
  | TArray {base_type} -> dependency es scope base_type
  | TMod {mod_type} -> dependency es scope mod_type (* TODO: redeclarations might cause additional dependencies, covered by folder ? - Test *)
  | TVar {flagged} -> dependency es scope flagged
  | TCon {flagged} -> dependency es scope flagged
  | TCau {flagged} -> dependency es scope flagged


let fold_dependencies scope this texp deps = match (dependency [] scope texp) with Some d when (List.mem d deps) -> deps | Some d -> d::deps | None -> deps

let dependency_collector scope = { default_folder with fold_texp = fold_dependencies scope;
                                                       fold_typedef = Folder.fold_id ;
                                                       fold_redeclared_typedef = Folder.fold_id;
                                 }

    
(* Folder to collect dependencies from local components *)
let local_deps scope c =
  let f = {(dependency_collector scope) with fold_extends = Folder.fold_id} in
  f.fold_composition f c []

(* Folder to collect dependencies from extends clauses *)
let superclass_deps scope c =                                    
  let f = {(dependency_collector scope) with fold_def = Folder.fold_id} in
  f.fold_composition f c []  
                                        
let rec fold_all f x = function
    l::r -> let x' = List.fold_left f x l in
            fold_all f x' r
  | [] -> x

(* create the local scope of a composition, taking into account local definitions and imports *)            
let local_scope scope name {imports;public;protected} =
  (* name of the actual scope *)
  let scope_name = match scope with [] -> [name] | {scope_name}::_ -> name::scope_name in
  let scope_tainted = public.extensions != [] || protected.extensions != [] in

  let name = function
      Short tds -> tds.td_name | Composition tds -> tds.td_name | Enumeration tds -> tds.td_name | OpenEnumeration tds -> tds.td_name | DerSpec tds -> tds.td_name | Extension tds -> tds.td_name in

  (* every import introduces a scope-entry, the unqualified import taints the respective entry *)
  let imported_names scope import = match import.commented with
      NamedImport {global;local} -> {scope_name=lunloc global; scope_tainted=false; scope_entries=StrSet.singleton local}::scope
    | Unnamed [] -> (* cannot happen, make ocamlc happy *) scope                                                                    
    | Unnamed name -> let local::global = List.rev (lunloc name) in {scope_name=global; scope_tainted=false; scope_entries=StrSet.singleton local}::scope
    | UnqualifiedImport name -> {scope_name=lunloc name; scope_tainted=true; scope_entries=StrSet.empty}::scope
  in
  
  let scope_entries =
    let add_entry x td = StrSet.add (name td.commented) x in
    fold_all add_entry StrSet.empty [public.typedefs; public.redeclared_types; protected.typedefs; protected.redeclared_types] (*TODO: do we need to check protected?*)
  in
  {scope_name; scope_tainted; scope_entries}::(List.fold_left imported_names scope imports)

    
    
let scan this td {found;scope} = match td with
  | Composition tds -> begin
                       let body = tds.type_exp in
                       
                       (* local extensions to the scope *)
                       let (local_scope::rest) = local_scope scope tds.td_name body in
                       
                       (* dependencies of the local extends-clauses *)
                       let superclass_dependencies = superclass_deps (local_scope::rest) body in
                       
                       (* dependencies of the local component definitions *)
                       let dependencies = local_deps (local_scope::rest) body in

                       (* scan dependencies of lexical children *)
                       let {found=found'} =
                         Composition.fold this tds.type_exp {scope=local_scope::rest; found}
                       in

                       (* create an artificial dependency: superclasses have to be resolved before the 
                          whole class can be resolved *)
                       let superclasses = Superclass local_scope.scope_name in
                       let inheritance = { local_name="Σ" ; from = [superclasses] ; element = [] } in

                       let component_def = {kontext_label=Path local_scope.scope_name; dependencies=inheritance::dependencies} in
                       let inheritance_def = {kontext_label=superclasses; dependencies=superclass_dependencies} in
                       
                       (* forget about the local scope and name again, remember lexical defs *)
                       {found=component_def::inheritance_def::found'; scope}
                     end
  | _ -> TD_Desc.fold this td {found;scope}

                      
let scan_dependencies scope typedef =
  let scanner = { default_folder with fold_typedef_desc = scan } in
  let { found } = scanner.fold_typedef scanner typedef { found = []; scope} in
  found
                                                                 

module KontextLabel = struct
         
  type t = kontext_label

  let compare = function Path(a) -> function Path(b) -> List.compare String.compare a b

  let hash = Hashtbl.hash
  let equal a b = a = b
  let default = Path []
end

module LexicalDepGraph = Graph.Persistent.Digraph.Concrete(KontextLabel)

module Scc = Graph.Components.Make(LexicalDepGraph)
                                                  
let topological_order deps =
  let add_dependency_edge source g dest =    
    LexicalDepGraph.add_edge g source dest
  in

  let add_dependency_edges source g {from} =    
    List.fold_left (add_dependency_edge source) g from
  in

  let rec add_downwards_dependency g = function
    | Path(name :: rest) -> LexicalDepGraph.add_edge (add_downwards_dependency g (Path rest)) (Path rest) (Path (name::rest))
    | _ -> g
  in
  
  let add_to_graph g { kontext_label ; dependencies } =
    let g' = add_downwards_dependency g kontext_label in
    List.fold_left (add_dependency_edges kontext_label) g' dependencies
  in    
  
  let g = List.fold_left add_to_graph LexicalDepGraph.empty deps in

  Scc.scc_list g
  
  

                       

                                      
