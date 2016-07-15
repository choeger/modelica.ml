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
open ModlibInter

let writes w i {lhs;rhs} =
  let name = Name.of_ptr lhs in
  match NameMap.Exceptionless.find name w with
    None -> NameMap.add name [i] w
  | Some is -> NameMap.add name (i::is) w

let writesMap prog =
  Array.fold_lefti writes NameMap.empty prog

let is_super {lhs} = match DQ.rear lhs with
    Some(_, `SuperClass _) -> true
  | _ -> false

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
  | RedeclareExtends -> r (* does not "read" a name, but depends on superclass-statements. needs to be handled later *) 
  | PInt | PReal | PString | PBool | PExternalObject | Empty _ -> r
  | PEnumeration _ -> r
  | Constr {arg} ->  reads r i {lhs; rhs=arg}
  | Close _ -> r                         
  | Reference n ->
    let sources = prefixes (Name.of_ptr lhs) in 
    let what = Name.of_list (lunloc n) in
    add_reads i (FirstOf {what; sources}) r

  | RootReference n -> add_reads i (Precisely (Name.of_list (lunloc n))) r
  | KnownPtr ptr -> add_reads i (Precisely (Name.of_ptr ptr)) r

let readsMap prog = Array.fold_lefti reads IntMap.empty prog

module GInt = struct include Int let hash i = i end

module DepGraph = Graph.Persistent.Digraph.Concrete(GInt)

module Scc = Graph.Components.Make(DepGraph)

exception NoClose
exception NormalizationError
exception IllegalRecursion of string

let topological_order w r a =

  let add_edge g from to_ = (*BatLog.logf "%s depends on %s\n" (show_class_stmt a.(from)) (show_class_stmt a.(to_)) ;*)
    if from = to_ then g else
      DepGraph.add_edge g to_ from
  in

  let find_super_classes =
    List.filter (fun j -> is_super a.(j)) 
  in

  let is_closer = function Close _ -> true
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

  let add_lookup_dependencies src g = List.fold_left (fun g dest -> add_edge g src dest) g in

  let rec add_local_deps src g = function
      [] -> g

    | (true, {source_name})::_ ->
      let ws = NameMap.find source_name w in
      let c = find_close ws in
      (* depend on the refinement being normalized *)
      (*BatLog.logf "%s can depend on %s\n" (show_class_stmt a.(src)) (show_class_stmt a.(c)) ;*)
      add_edge g src c                         

    (* when the empty source name could not be refined, it will not match, since the root-package is never tainted *)
    | (false, {source_name})::srcs when source_name=DQ.empty -> add_local_deps src g srcs

    | (false, {source_name})::srcs ->
      (* BatLog.logf "Searching writer of %s\n" (Name.show source_name) ; *)
      try 
        let ws = NameMap.find source_name w in
        (* BatLog.logf "%s can depend on superclasses of %s\n" (show_class_stmt a.(src)) (Name.show source_name) ; *)   
        (* no refinement found in that scope, just depend on the superclasses *)
        add_local_deps src (add_lookup_dependencies src g (find_super_classes ws)) srcs
      with
        Not_found ->
        (BatLog.logf "Could not find definition of %s under %d entries\n" (Name.show source_name) (NameMap.cardinal w);
         NameMap.iter (fun k _ -> if Name.size k = Name.size source_name then BatLog.logf "  Candidate: %s\n" (Name.show k)) w ;
         raise NormalizationError)
  in

  let add_dep i g d =
    match d with
    | Precisely n -> let (refined, source) = refine {source_name=DQ.empty; required=n} in
      add_local_deps i g [(refined, source)]

    | FirstOf {what ; sources } ->
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
        [] -> (*BatLog.logf "No empty statement for %s\n" (Name.show lhs) ;*) g

      (* single writer, add dependency to parent opener *) 
      | [j] -> begin match DQ.rear lhs with Some(xs,x) -> add_empty_creator g i xs | None -> g end 

      (* In case of multiple writers there needs to be a Empty statement *)
      | (fst::_) as js ->
        try 
          let j = List.find (fun j -> is_empty a.(j).rhs) js in add_edge g i j
        with
          Not_found -> BatLog.logf "No empty rhs for %s\n" (show_class_ptr a.(fst).lhs) ; raise NormalizationError
                         
    else (BatLog.logf "Could not add %s to open-statement, no such statement found.\n" (Name.show lhs) ; g)
  in

  (* Find the statement responsible for closing a scope out of possible multiple writers *)
  let rec add_to_closer g i lhs =
    if NameMap.mem lhs w then
      match NameMap.find lhs w with
        [] -> raise NoClose
      | [j] -> begin match DQ.rear lhs with Some(xs,x) -> add_to_closer g i xs | None -> g end
      | ws ->
        (*BatLog.logf "searching closer for: %s\n%!" (Name.show lhs) ;*)
        let c = find_close ws in
        add_edge g c i
    else (BatLog.logf "Could not add %s to close-statement, no such statement found.\n" (Name.show lhs) ; g)
  in

  let rec opens_scope = function
      Empty _ -> true
    | Constr {arg} -> opens_scope arg
    | _ -> false
  in

  (* add all the "upwards" dependencies to ensure 
     the scope chain is properly setup 
     (basically just ensure that parents in the form 
     of 'lhs := reference' are normalized first *)
  let rec scope_deps g i lhs rhs = match (DQ.rear lhs) with
    | Some(q, x) when NameMap.mem lhs w ->
      let g' = add_empty_creator g i lhs in
      let g'' =  add_to_closer g' i lhs             
      in
      begin match rhs with               
        (* If this is a close statement, add a reverse dependency 
           to the parent's close statement *)
          Close _ when NameMap.mem q w -> add_to_closer g'' i q

        | t when (opens_scope t) && (NameMap.mem q w) ->
          add_empty_creator g'' i q

        (* create dependency on parent superclass for modifications *)
        | RedeclareExtends ->
          let ws = NameMap.find q w in
          let supers = List.filter (fun i -> is_super a.(i)) ws in
          List.fold_left (fun g super -> add_edge g i super) g'' supers 
        | _ -> g''
      end
    | _ -> g
  in

  let add_deps g (i, ds) = List.fold_left (add_dep i) g ds in

  let add_scope_deps g i {lhs;rhs} =    
    (* `Any as the last name element 
       means we need to resolve the parent superclass(es) first for the
       stratification *)
    let g' = match DQ.rear lhs with
        Some (q, `Any _) ->
        let ws = NameMap.find (Name.of_ptr q) w in
        let supers = List.filter (fun i -> is_super a.(i)) ws in          
        let g' = add_to_closer g i (Name.of_ptr lhs) in
        List.fold_left (fun g super ->
            add_edge g i super) g' supers          
      | _ -> g
    in
    scope_deps (DepGraph.add_vertex g' i) i (Name.of_ptr lhs) rhs in

  let g = Array.fold_lefti add_scope_deps DepGraph.empty a in

  let g = List.fold_left add_deps g (IntMap.bindings r) in

  let sccs = Scc.scc_list g in

  (* SCC processing:
       * non-trivial SCC?
       |
       |__no__ : Ok, add singleton to prog
       |
       |__yes_ : * Superclasses contained?  
                 |
                 |__no__ : * For each statement:
                 |         | Close-statement?
                 |         |
                 |         |__yes_ : Do nothing, just copy, all other statements won't unfold anything yet
                 |         |
                 |         |__no__ : Create Self() and Unfold() statement
                 |
                 |__yes_ : * Remove incoming edges to (hierachically) highest superclass process subgraph
  *)                           
  let rec process_scc prog graph scc =
    let superclasses = List.sort (fun i j -> Int.compare (DQ.size a.(i).lhs) (DQ.size a.(j).lhs)) (List.filter (fun i -> is_super a.(i)) scc) in

    match superclasses with
      [] -> (self_stmts (unfold_stmts prog scc) scc)
    | fst::_ -> begin
        let vs = IntSet.of_list scc in
        (*      BatLog.logf "Breaking SCC with %d vertices.\n" (IntSet.cardinal vs);
                BatLog.logf "Removing dependencies on %s\n" (show_class_ptr a.(fst).lhs) ;
        *)      
        let copy_edges v1 v2 g =
          (* copy edges from the subgraph, ignore incoming edges to the highest superclass *)
          if v1 != fst && IntSet.mem v1 vs && IntSet.mem v2 vs then begin
            (*BatLog.logf "Keeping dependency from\n  %s\nto\n  %s\n" (sc a.(v2)) (sc a.(v1));*)
            (DepGraph.add_edge g v1 v2)
          end else g
        in

        let subgraph = DepGraph.fold_edges copy_edges graph (List.fold_left DepGraph.add_vertex DepGraph.empty scc) in
        let sccs' = Scc.scc_list subgraph in
        reorder_sccs prog sccs'          
      end		  

  and unfold_stmts prog = function [] -> prog
                                 | i::scc when is_super a.(i) -> raise (IllegalRecursion (show_class_ptr (a.(i).lhs)))
                                 | i::scc when is_closer a.(i).rhs -> unfold_stmts (a.(i)::prog) scc
                                 | i::scc -> unfold_stmts ({lhs=a.(i).lhs; rhs=a.(i).rhs}::prog) scc
                                               
  and self_stmts prog = function [] -> prog
                                 | i::scc when is_super a.(i) -> raise (IllegalRecursion (show_class_ptr (a.(i).lhs)))
                                 | i::scc when is_closer a.(i).rhs -> self_stmts (a.(i)::prog) scc
                                 | i::scc -> self_stmts ({lhs=a.(i).lhs; rhs=PEnumeration StrSet.empty}::prog) scc

  and reorder_sccs prog = function
    | [] -> prog 
    | [i]::sccs -> reorder_sccs (a.(i)::prog) sccs                                
    | scc::sccs -> reorder_sccs (process_scc prog g scc) sccs
  in

  reorder_sccs [] sccs

let preprocess prog =
  let a = Array.of_list prog in
  let wm = writesMap a in
  (Array.of_list (topological_order wm (readsMap a) a))
