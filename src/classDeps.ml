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

module StdFormat = Format
open Batteries
module Format = StdFormat
open Utils
open Motypes

let writes w i {lhs;rhs} =
  let name = Name.of_ptr lhs in
  match NameMap.Exceptionless.find name w with
    None -> NameMap.add name [i] w
  | Some is -> NameMap.add name (i::is) w
                           
let writesMap prog =
  Array.fold_lefti writes NameMap.empty prog

type first_of = { what : Name.t ; sources : Name.t list } [@@deriving show, yojson]
                   
type dependency_source = {
  source_name : Name.t;
  required : Name.t;
} [@@deriving show, yojson]

type external_dependency = dependency_source list [@@deriving show, yojson]

type external_dependencies = external_dependency list [@@deriving show, yojson]

                                             
type read_dep = Precisely of Name.t
              | FirstOf of first_of

let rec prefixes_ ps n = match DQ.rear n with
    None -> n::ps
  | Some (r, x) -> prefixes_ (n :: ps) r
                                             
let prefixes n = List.rev (prefixes_ [] n)

let add_reads i d r = IntMap.modify_def [] i (List.cons d) r 

exception IllegalRedeclaration                                          
                                        
let rec reads r i {lhs; rhs} =  
  match rhs with
  | RedeclareExtends -> begin match DQ.rear lhs with
                              | Some (scope, `SuperClass _) -> begin match DQ.rear scope with
                                                                     | Some (parent, _) -> add_reads i (Precisely (Name.of_ptr parent)) r
                                                                     | _ -> raise IllegalRedeclaration
                                                               end
                              | _ -> raise IllegalRedeclaration
                        end
  | PInt | PReal | PString | PBool | PExternalObject | Empty _ -> r
  | PEnumeration _ -> r
  | Constr {arg} ->  reads r i {lhs; rhs=arg}
  | Close -> r                         
  | Reference n ->
     let sources = prefixes (Name.scope_of_ptr lhs) in 
     let what = Name.of_list (lunloc n) in
     add_reads i (FirstOf {what; sources}) r
                              
  | RootReference n -> add_reads i (Precisely (Name.of_list (lunloc n))) r

let readsMap prog = Array.fold_lefti reads IntMap.empty prog
                                  
module GInt = struct include Int let hash i = i end
                                  
module DepGraph = Graph.Persistent.Digraph.Concrete(GInt)

module Scc = Graph.Components.Make(DepGraph)

exception NoClose
                                  
let topological_order w r a =

  let is_super {lhs} = match DQ.rear lhs with
      Some(_, `SuperClass _) -> true
    | _ -> false
  in

  let find_super_classes =
    List.filter (fun j -> is_super a.(j)) 
  in
  
  let is_closer = function Close -> true
                         | _ -> false
  in
  
  let find_close =
    function
    | [] -> raise NoClose
    | [j] -> j (* single writer, no real close statement *)
    (* In case of multiple writers there needs to be a close statement *)
    | js -> List.find (fun j -> is_closer a.(j).rhs) js 
  in
  
  let rec refine_ h s = match DQ.front s.required with 
      None -> (NameMap.mem s.source_name w, s)
    | Some (x,xs) ->  let source_name = (DQ.snoc s.source_name x)  in
                      if NameMap.mem source_name w then refine_ true {source_name; required=xs} else (h,s)
  in
  
  let refine s = refine_ false s in

  let add_lookup_dependencies src g = List.fold_left (fun g dest -> DepGraph.add_edge g dest src) g in
  
  let rec add_local_deps src g = function
      [] -> g

    | (true, {source_name})::_ ->
       let ws = NameMap.find source_name w in
       let c = find_close ws in
       (* depend on the refinement being normalized *)
       DepGraph.add_edge g c src                         

    (* when the empty source name could not be refined, it will not match, since the root-package is never tainted *)
    | (false, {source_name})::srcs when source_name=DQ.empty -> add_local_deps src g srcs
                         
    | (false, {source_name})::srcs ->
       let ws = NameMap.find source_name w in
       (* no refinement found in that scope, just depend on the superclasses *)
       add_local_deps src (add_lookup_dependencies src g (find_super_classes ws)) srcs
  in

  let add_dep i g d =    
    match d with
    | Precisely n -> let (refined, source) = refine {source_name=DQ.empty; required=n} in
                     add_local_deps i g [(refined, source)]
                                                                          
    | FirstOf ({what ; sources } as fo) ->
       let srcs = List.map (fun source_name -> {source_name; required=what}) sources in
       let refined = List.map refine srcs in       
       add_local_deps i g refined
  in

  (* Find the statement responsible for creating a scope out of possible multiple writers *)
  let rec add_empty_creator g i lhs =
    let rec is_empty = function Empty _ -> true
                              | Constr {arg} -> is_empty arg
                              | _ -> false
    in
    if NameMap.mem lhs w then
    match NameMap.find lhs w with
      [] -> g

    (* single writer, add dependency to parent opener *) 
    | [j] -> begin match DQ.rear lhs with Some(xs,x) -> add_empty_creator g i xs | None -> g end 

    (* In case of multiple writers there needs to be a Empty statement *)
    | js -> let j = List.find (fun j -> is_empty a.(j).rhs) js in DepGraph.add_edge g j i
    else (BatLog.logf "Could not add %s to open-statement, no such statement found.\n" (Name.show lhs) ; g)
  in

  (* Find the statement responsible for closing a scope out of possible multiple writers *)
  let rec add_to_closer g i lhs =
    if NameMap.mem lhs w then
    match NameMap.find lhs w with
      [] -> raise NoClose
    | [j] -> begin match DQ.rear lhs with Some(xs,x) -> add_to_closer g i xs | None -> g end
    | ws -> let c = find_close ws in
            DepGraph.add_edge g i c
    else (BatLog.logf "Could not add %s to close-statement, no such statement found.\n" (Name.show lhs) ; g)
  in
  
  (* add all the "upwards" dependencies to ensure the scope chain is properly setup 
     (basically just ensure that parents in the form of 'lhs := reference' are normalized first *)
  let rec scope_deps g i lhs rhs = match (DQ.rear lhs) with
    | Some(q, _) when NameMap.mem lhs w ->
       let g' = add_empty_creator g i lhs in
       let g'' = add_to_closer g' i lhs in
       (* If this is a close statement, add a reverse dependency to the parent's close statement *)
       begin match rhs with               
               Close when NameMap.mem q w -> add_to_closer g'' i q
             | Empty _ when NameMap.mem q w -> add_empty_creator g'' i q
             | _ -> g''
       end
    | _ -> g
  in
                             
  let add_deps g (i, ds) = List.fold_left (add_dep i) g ds in

  let add_scope_deps g i {lhs;rhs} = scope_deps (DepGraph.add_vertex g i) i (Name.of_ptr lhs) rhs in
  
  let g = Array.fold_lefti add_scope_deps DepGraph.empty a in
      
  let g = List.fold_left add_deps g (IntMap.bindings r) in

  let sccs = Scc.scc_list g in
  
  BatLog.logf "Got %d vertices and %d edges in %d strongly connected components in the dependency graph out of %d statements\n"
              (DepGraph.nb_vertex g) (DepGraph.nb_edges g) (List.length sccs) (Array.length a) ;

  let rec prepare_scc prog = function [] -> prog
                                    | i::scc when (is_super a.(i)) -> prepare_scc prog scc
                                    | i::scc when not (is_closer a.(i).rhs) -> prepare_scc ({lhs=a.(i).lhs; rhs=Delay a.(i).rhs}::prog) scc
                                    | i::scc -> prepare_scc prog scc
  in

  let rec append_scc prog = function [] -> prog
                                   | i::scc when (is_super a.(i)) -> append_scc prog scc
                                   | i::scc -> append_scc (a.(i)::prog) scc in

  let rec append_superclasses prog = function [] -> prog
                                            | i::scc when (is_super a.(i)) -> append_superclasses (a.(i)::prog) scc
                                            | i::scc -> append_superclasses prog scc
  in
  
  let handle_scc prog scc =
    prepare_scc (append_scc (append_superclasses prog scc) scc) scc 
  in
      
  let rec reorder_sccs prog = function
    | [] -> prog 
    | [i]::sccs -> reorder_sccs (a.(i)::prog) sccs                                
    | scc::sccs -> reorder_sccs (handle_scc prog scc) sccs
  in
  
  reorder_sccs [] sccs
 
let preprocess prog =
  let a = Array.of_list prog in
  (Array.of_list (topological_order (writesMap a) (readsMap a) a))
