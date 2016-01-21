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
open Location
open Report
module Inter = ModlibInter
module Normalized = ModlibNormalized
open Inter
open Syntax
open Normalized
    
exception EmptyName

type history_entry_kind = [`ClassMember of string | `SuperClass of int]

type history_entry_t = { entry_structure : object_struct; entry_kind : history_entry_kind}

type trace_t = Path.t list

type history_t = history_entry_t DQ.t

type lookup_state = {
  history : history_t; (** The visited classes *)
  trace : trace_t; (** The found references *)
  current_path : Path.t ; (** The path to the current class value *)
  current_attr : flat_attributes ;
  current_ref : Syntax.known_ref; (** The search request as a resolved component *)
}

let path_of_history = DQ.map (fun {entry_kind} -> (entry_kind :> Path.elem_t)) 

(** Find the first (from bottom) class which is a prefix of $path in $history and the corresponding suffix 
    If the last entry is a superclass, the corresponding extending class is returned.
    This should yield the context of a given path relativ to the current search history.
*)
let rec find_prefix (history, path) =
  let rec ip p1 p2 =
    match DQ.front p1 with None -> Some p2 | Some(x,xs) -> begin match DQ.front p2 with Some(y,ys) when y = x -> ip xs ys | _ -> None end
  in
  let rec drop_superclasses history = match DQ.rear history with
      Some(history, {entry_kind=`SuperClass _}) -> drop_superclasses history
    | _ -> history
  in
  match DQ.rear history with
    Some (history, {entry_kind=`SuperClass _; entry_structure=os}) ->
    begin match ip os.source_path path with
        None -> find_prefix (history, path)
      | Some suffix -> (drop_superclasses history, suffix)
    end
  | Some (history, {entry_kind=`ClassMember _; entry_structure=os}) ->
    begin match ip os.source_path path with
        None -> find_prefix (history, path)
      | Some suffix -> (history, suffix)
    end
  | None -> raise (Failure "Fatal error, no root-scope found")
  
let rec get_class_element_in ({current_path; current_ref} as state) {Normalized.class_members; super; fields} x xs =
  if StrMap.mem x.ident.txt class_members then begin
    let current_path = (DQ.snoc current_path (`ClassMember x.ident.txt)) in
    let current_ref = DQ.snoc current_ref {kind = CK_Class; component=x} in
    let r = get_class_element {state with current_path; current_ref} (StrMap.find x.ident.txt class_members).class_ xs in
    match r with
      `NothingFound -> (`PrefixFound {not_found=xs; found=current_path})      
    | r -> r
  end
  else if StrMap.mem x.ident.txt fields then begin
    let current_path = (DQ.snoc current_path (`FieldType x.ident.txt)) in
    let current_ref = DQ.snoc current_ref {Syntax.kind = CK_Continuous; component=x} in
    let r = (get_class_element {state with current_path; current_ref} (StrMap.find x.ident.txt fields).field_class xs) in
    match r with
      `NothingFound -> (`PrefixFound {not_found=xs; found=current_path})      
    | r -> r
  end
  else ( pickfirst_class state (x::xs) (IntMap.bindings super) )

and get_class_element_os ({history; trace; current_path} as state) ({public;protected} as os) x xs =  
  let history = match DQ.rear current_path with
      Some(_, `SuperClass i) -> DQ.snoc history {entry_structure=os; entry_kind=`SuperClass i}
    | Some(_, `ClassMember x) -> DQ.snoc history {entry_structure=os; entry_kind=`ClassMember x}
    | Some(_, x) -> raise (Failure ("Unexpected path element for object_struct: " ^ (Path.show_elem_t x)))
    | None -> raise EmptyName
  in  
  let f = get_class_element_in {state with history} public x xs in
  match f with
    `NothingFound ->
    let current_path = DQ.snoc current_path `Protected in
    get_class_element_in {state with history; current_path} protected x xs
  | _ as r -> r

and pickfirst_class state name = function
    [] -> `NothingFound
  | (k,v)::vs ->
    let current_path = DQ.snoc state.current_path (`SuperClass k) in
    let f = get_class_element {state with current_path} v.class_ name in
    begin match f with
        `NothingFound -> pickfirst_class state name vs
      | r -> r
    end

and get_class_element ({history;trace;current_path} as state) e p =
  let open Normalized in 

  let ck_of_var = 
    let open Flags in
    function None -> CK_Continuous | Some Constant -> CK_Constant | Some Parameter -> CK_Parameter | Some Discrete -> CK_Discrete
  in
  
  let finish_component state = match DQ.rear state.current_ref with
    (* update last component reference with collected flat attribute *)
      None | Some (_,{kind=CK_Class}) -> {state with current_attr = no_attributes}
    | Some(xs, x) -> {state with current_ref = (DQ.snoc xs {x with kind=ck_of_var state.current_attr.fa_var});
                                 current_attr = no_attributes}
  in
  
  match e with
  | Class os ->
    let state = finish_component state in
    begin match p with
        [] -> `Found {found_value=e; found_path=state.current_path; found_ref=state.current_ref; found_visible=true; found_replaceable=false}
      | x::xs -> get_class_element_os state os x xs 
    end

  (* we might encounter recursive elements *)
  | Recursive rec_term -> `Recursion {rec_term; search_state={found = current_path; not_found = p}}

  (* follow global references through self to implement redeclarations *)
  | DynamicReference g | GlobalReference g ->
    let q = DQ.of_enum (Enum.filter (function (`FieldType _| `ClassMember _) -> true | _ -> false) (DQ.enum g)) in

    (* Append to trace, TODO: found_visible/found_replaceable *)
    let trace = g::trace in
    (* History and suffix of searched path 
           i.e. path[last[h']] ++ q' == q
    *)
    let (history', q') = find_prefix (history, q) in
        
    (* Create the new search task *)
    let new_prefix = Enum.filter_map (function (`ClassMember x | `FieldType x) -> Some {ident={txt=x;loc=none};subscripts=[]} | _ -> None) (DQ.enum q') in    
    let p' = List.of_enum (Enum.append new_prefix (List.enum p)) in

    let current_path = path_of_history history' in
    begin match DQ.rear history' with
      Some(history, {entry_structure}) ->
      get_class_element {state with current_path;history;trace} (Class entry_structure) p
    | None -> raise (Failure "history not setup properly. First element (root) needs to have empty source path!")
    end

  (* Replaceable/Constr means to look into it *)
  | Replaceable v -> get_class_element state v p    
  | Constr {arg} -> get_class_element state arg p
  | _ -> `NothingFound
    

let lookup o p =
  let open Normalized in
  match p with
    [] -> (`Found {found_value = Class {empty_object_struct with public = o}; found_path = DQ.empty; found_ref=DQ.empty; found_visible=true; found_replaceable=false}) ;
  | x::xs ->
    let state = {history = DQ.singleton {entry_structure = {empty_object_struct with public = o}; entry_kind = `ClassMember ""};
                 trace = [] ;
                 current_ref = DQ.empty;
                 current_attr = no_attributes;
                 current_path = DQ.empty}                  
    in
    get_class_element_in state o x xs

