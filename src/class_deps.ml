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

type dependency_source = {
  source_label : kontext_label;
  required_elements : string list;
}
                                          
type dependency = {
  local_name : string;
  from : dependency_source list;
}

type lexical_typedef = {
  kontext_label : kontext_label;
  dependencies : dependency list;
}

type scope_entry = {
  scope_name : string list ;
  scope_tainted: bool;
  scope_entries :  string StrMap.t;
}

type scope = scope_entry list
                                  

(** Find all possible global names of a given identifier in the given scope *)
let rec find x required_elements = function
    (* when x is in the scope, tainted does not matter, it shadows all entries above *)
    {scope_entries; scope_name}::rest when StrMap.mem x scope_entries -> [{source_label = Path ((StrMap.find x scope_entries)::scope_name) ; required_elements}]
  (* when the scope is not tainted, use "normal" lexical scoping *)
  | {scope_tainted=false}::rest -> find x required_elements rest
  (* when the scope is tainted, we have to consider it *)
  | {scope_tainted=true; scope_name}::rest -> {source_label = Superclass scope_name ; required_elements = x::required_elements} ::(find x required_elements rest)
  | [] -> []
                         
type scanner_result = {
  found : lexical_typedef list;
  scope : scope;
}

let builtin = function
  | "ExternalObject" | "String" | "Real" | "Boolean" | "Integer" -> true
  | _ -> false
                        
(** Compute a dependency from a type-expression *)
let rec dependency es scope = function
  | TName [x] when builtin x.txt -> None
  | TName [x] -> let from = find x.txt es scope in Some {local_name = x.txt ; from }
  | TRootName [x]-> Some {from = [{source_label = Path(x.txt :: es); required_elements = []}] ; local_name=x.txt}
  | TName(t::base) -> dependency (t.txt::es) scope (TName base)
  | TRootName(t::base) -> dependency (t.txt::es) scope (TRootName base)
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

    | NamedImport {global=[]; _} | Unnamed [] -> (* cannot happen, make ocamlc happy *) scope                                                                    

    (* in the case of a renaming import, pick up the substitution *)
    | NamedImport {global;local} -> let locals::global = List.rev (lunloc global) in
                                    {scope_name=global; scope_tainted=false; scope_entries=StrMap.singleton local locals}::scope

    | Unnamed name -> let local::global = List.rev (lunloc name) in {scope_name=global; scope_tainted=false; scope_entries=StrMap.singleton local local}::scope
    | UnqualifiedImport name -> {scope_name=lunloc name; scope_tainted=true; scope_entries=StrMap.empty}::scope
  in
  
  let scope_entries =
    let add_entry x td = let n = name td.commented in StrMap.add n n x in
    fold_all add_entry StrMap.empty [public.typedefs; public.redeclared_types; protected.typedefs; protected.redeclared_types] (*TODO: do we need to check protected?*)
  in
  {scope_name; scope_tainted; scope_entries}::(List.fold_left imported_names scope imports)
        
let scan this td {found;scope} = match td with
  | Enumeration tds -> begin
                       (* enumerations do not depend on other types *)
                       let kontext_label = match scope with
                           parent::_ -> Path (tds.td_name::parent.scope_name)
                         | _ -> Path [tds.td_name]
                       in
                       let typedef = {kontext_label; dependencies=[]} in
                       {found = typedef::found; scope}                     
                     end
  | Short tds -> begin
                 let kontext_label = match scope with
                     parent::_ -> Path (tds.td_name::parent.scope_name)
                   | _ -> Path [tds.td_name]
                 in

                 (* scan dependencies of the rhs *)
                 let rhs = tds.type_exp in
                 let f = (dependency_collector scope) in
                 let dependencies = f.fold_texp f rhs [] in
                 let typedef = {kontext_label; dependencies} in
                 {found = typedef::found; scope}
               end
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
                       let superclass_label = Superclass local_scope.scope_name in
                       let superclasses = { source_label = superclass_label ; required_elements = []} in
                       let inheritance = { local_name="Σ" ; from = [superclasses] } in

                       let component_def = {kontext_label=Path local_scope.scope_name; dependencies=inheritance::dependencies} in
                       let inheritance_def = {kontext_label=superclass_label; dependencies=superclass_dependencies} in
                       
                       (* forget about the local scope and name again, remember lexical defs *)
                       {found=component_def::inheritance_def::found'; scope}
                     end
  | _ -> TD_Desc.fold this td {found;scope}


let rec prefix a = function
    [] -> List.is_empty a
  | x::xs -> match a with
               [] -> true
             | y::ys when y = x -> prefix ys xs 
             | y::_ -> false                         
               
let lexically_below p = function
    Superclass(r) | Path r -> prefix (List.rev r) p
                          
let lexically_smaller = function
    Superclass(r) | Path r -> lexically_below (List.rev r)
                      
module KontextLabel = struct
         
  type t = kontext_label

  (* create a string list from a label *)
  let pp = function Path(a) -> a
                  | Superclass a -> "Σ"::a
             
  let compare a b = List.compare String.compare (pp a) (pp b)                                                                                              

  let hash = Hashtbl.hash
  let equal a b = a = b
  let default = Path []
end

module LexicalDepGraph = Graph.Persistent.Digraph.Concrete(KontextLabel)

module Scc = Graph.Components.Make(LexicalDepGraph)

module LabelMap = Map.Make(KontextLabel)

module LabelSet = Set.Make(KontextLabel)

let rec refine_dependency_source defs = function
    { source_label = Path(p); required_elements = x::xs } when LabelSet.mem (Path(x::p)) defs ->
    refine_dependency_source defs { source_label = Path(x::p) ; required_elements = xs } 
  | d -> d 

let refine_dependency defs {local_name; from} = {local_name; from=List.map (refine_dependency_source defs) from}
                                                  
let scan_dependencies scope typedef =
  let scanner = { default_folder with fold_typedef_desc = scan } in
  let { found } = scanner.fold_typedef scanner typedef { found = []; scope} in
  let add = fun s d -> LabelSet.add d.kontext_label s in
  let set = List.fold_left add LabelSet.empty found in
  let refine d = {d with dependencies = List.map (refine_dependency set) d.dependencies} in
  List.map refine found

let subgraph vs g =
  let add_succ pred succ g = if LabelSet.mem succ vs then LexicalDepGraph.add_edge g pred succ else g in
  let retain v g' = LexicalDepGraph.fold_succ (add_succ v) g v g' in
  LabelSet.fold retain vs LexicalDepGraph.empty

let cut_superclass_deps g group =
  (* try to cut all dependencies to a superclass if that dependency is lexically smaller than (i.e. "inside") the inheriting class *)
  let is_superclass = function Superclass _ -> true | _ -> false in
  
  let sigmas = LabelSet.of_list (List.filter is_superclass group) in
  let length_orig = List.length group in
  if LabelSet.is_empty sigmas then [group] else    
     let vs = LabelSet.of_list group in
     let g' = subgraph vs g in
     Printf.printf "Got %d vertices and %d edges in the scc sub-graph\n" (LexicalDepGraph.nb_vertex g') (LexicalDepGraph.nb_edges g') ;
     let delete_incoming sigma incoming g = if (lexically_smaller incoming sigma) then
                                              LexicalDepGraph.remove_edge g incoming sigma
                                            else g in
     let delete_back_deps sigma g = LexicalDepGraph.fold_pred (delete_incoming sigma) g sigma g in
     let cutted = LabelSet.fold delete_back_deps sigmas g' in

     let ret = Scc.scc_list cutted in
     Printf.printf "Split a group of %d vertices into %d sub-groups\n" length_orig (List.length ret) ; ret
                                                                                                         
let prep_scc g = function
    [] -> []
  | x::[] -> [x::[]]
  | x::xs -> cut_superclass_deps g (x::xs)
                  
let topological_order deps =
  let add_dependency_edge source g dest = 
    LexicalDepGraph.add_edge g source dest.source_label
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

  Printf.printf "Got %d vertices and %d edges in the dependency graph\n" (LexicalDepGraph.nb_vertex g) (LexicalDepGraph.nb_edges g) ;
  
  List.flatten (List.map (prep_scc g) (Scc.scc_list g))
  
  

                       

                                      
