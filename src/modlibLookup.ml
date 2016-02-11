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
module Inter = ModlibInter
module Normalized = ModlibNormalized
open Inter
open Syntax
open Normalized
    
exception EmptyName
exception ExpansionException of string
exception ForwardFailure of Path.elem_t
exception EmptyScopeHistory

type history_entry_kind = [`FieldType of string | `ClassMember of string | `SuperClass of int] [@@deriving yojson,show]

type history_entry_t = { entry_structure : object_struct; entry_kind : history_entry_kind} [@@deriving yojson]

let pp_history_entry_t fmt = function
    { entry_structure ; entry_kind = `ClassMember x} -> Format.fprintf fmt "class %s = %a" x Path.pp entry_structure.source_path
  | { entry_structure ; entry_kind = `SuperClass i} -> Format.fprintf fmt "super %d = %a" i Path.pp entry_structure.source_path

type trace_t = Path.t DQ.t [@@deriving show,yojson]

type history_t = history_entry_t DQ.t [@@deriving show,yojson]

type lookup_state = {
  history : history_t; (** The visited classes *)
  trace : trace_t; (** The found references *)
  replaceable : bool; (** Visited a replaceable declaration *)
  current_path : Path.t ; (** The path to the current class value *)
  current_attr : flat_attributes ;
  current_ref : Syntax.known_ref; (** The search request as a resolved component *)
  current_scope : int; (** Relative current scope *)
} [@@deriving show,yojson]

let empty_lookup_state = {history=DQ.empty; trace=DQ.empty; replaceable = false ; current_path=Path.empty; current_attr=no_attributes; current_ref=DQ.empty; current_scope=0}

let dump_lookup_state {current_path} = Printf.sprintf "Last class: %s\n" (Path.show current_path)

type lookup_success_struct = { lookup_success_state : lookup_state ;
                               lookup_success_value : class_value ;
                             } [@@deriving show,yojson]

type lookup_error_struct = { lookup_error_state : lookup_state ;
                             lookup_error_todo : component list }
                           [@@deriving show,yojson]

type lookup_recursion_struct = { lookup_recursion_term : rec_term ;
                                 lookup_recursion_state : lookup_state ;
                                 lookup_recursion_todo : component list } [@@deriving show,yojson]

type lookup_result = Success of lookup_success_struct 
                   | Recursion of lookup_recursion_struct
                   | Error of lookup_error_struct
  [@@deriving show,yojson]

let path_of_history h = match DQ.front h with
    Some(root,classes) ->
    (* First entry is the unnamed root class *)
    DQ.map (fun {entry_kind} -> (entry_kind :> Path.elem_t)) classes
  | _ -> Path.empty (* Should not happen, but empty path is safe default *)

(** wrap a history of visited classes into a new lookup state *)
let state_of_history history = {history;
                                replaceable = false;
                                trace = DQ.empty ;
                                current_ref = DQ.empty;
                                current_attr = no_attributes;
                                current_scope = 0;
                                current_path = path_of_history history}

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
    Some (history', {entry_kind=`SuperClass _; entry_structure=os}) ->
    begin match ip os.source_path path with
        None -> find_prefix (history', path)
      | Some suffix -> (drop_superclasses history, suffix)
    end
  | Some (history', {entry_kind=`FieldType _ | `ClassMember _; entry_structure=os}) ->
    begin match ip os.source_path path with
        None -> find_prefix (history', path)
      | Some suffix -> (history, suffix)
    end
  | None -> raise (Failure "Fatal error, no root-scope found")

let append_to_history {history;current_path} entry_kind os =
  DQ.snoc history {entry_structure=os; entry_kind}
                
let rec get_class_element_in state {Normalized.class_members; super; fields} x xs =  
  if StrMap.mem x.ident.txt class_members then begin
    let current_ref = DQ.snoc state.current_ref {kind = CK_Class; component=x} in
    get_class_element {state with current_ref} (`ClassMember x.ident.txt) (StrMap.find x.ident.txt class_members).class_ xs
  end
  else if StrMap.mem x.ident.txt fields then begin
    let current_ref = DQ.snoc state.current_ref {Syntax.kind = CK_Continuous; component=x} in
    get_class_element {state with current_ref} (`FieldType x.ident.txt) (StrMap.find x.ident.txt fields).field_class xs
  end
  else begin
    (*BatLog.logf "Looking in %d superclasses for %s\n" (IntMap.cardinal super) x.ident.txt ;*)
    (pickfirst_class state (x::xs) (IntMap.bindings super) )
  end
  
and get_class_element_os state ({public;protected} as os) x xs =
  (*BatLog.logf "Looking in: %s\n" (Path.show os.source_path) ;*)
  let f = get_class_element_in state public x xs in
  match f with
    Error {lookup_error_state={current_ref}} when current_ref == state.current_ref ->
    (* Nothing found, search protected section *)
    let current_path = DQ.snoc state.current_path `Protected in
    get_class_element_in {state with current_path} protected x xs
  | _ as r -> r (* Something found *)

and pickfirst_class state name = function
    [] -> Error {lookup_error_state=state; lookup_error_todo=name}
  | (k,v)::vs ->
    (*BatLog.logf "Superclass %d = %s\n" k (show_class_value v.class_) ;*)
    let f = get_class_element state (`SuperClass k) v.class_ name in
    begin match f with
        Error {lookup_error_state={current_ref}} when current_ref == state.current_ref ->
        (* Nothing found, search next superclass *)
        pickfirst_class state name vs
      | r -> r
    end

(**
  $state : lookup state 
  $k : kind of this class value
  $p : components todo
*)
and get_class_element state (k:history_entry_kind) e p =
  let open Normalized in 
  let current_path = Path.snoc state.current_path (k :> Path.elem_t) in
  let state = {state with current_path} in

  let ck_of_var = 
    let open Flags in
    function None -> CK_Continuous | Some Constant -> CK_Constant | Some Parameter -> CK_Parameter | Some Discrete -> CK_Discrete
  in
  
  let finish_component state = match DQ.rear state.current_ref with    
    (* update last component reference with collected flat attribute *)
      None | Some (_,{kind=CK_Class}) -> {state with current_attr = {no_attributes with fa_sort = state.current_attr.fa_sort}}
    | Some(xs, x) -> {state with current_ref = (DQ.snoc xs {x with kind=ck_of_var state.current_attr.fa_var})}
  in
  
  let rec helper state = function
  | Class os ->
    (*BatLog.logf "Looking in class: %s\n" (Path.show os.source_path) ;*)
    let state = finish_component state in
    begin match p with
        [] -> Success {lookup_success_value=e; lookup_success_state=state}
      | x::xs ->
        let history = append_to_history state k os in
        get_class_element_os {state with history; current_path} os x xs 
    end

  (* we might encounter recursive elements *)
  | Recursive lookup_recursion_term -> Recursion {lookup_recursion_term;
                                                  lookup_recursion_state=state;
                                                  lookup_recursion_todo=p}

    (* follow global references through self to implement redeclarations *)
  | DynamicReference g | GlobalReference g ->
    BatLog.logf "Continuing lookup in %s\n" (Path.show g) ;
    let q = DQ.of_enum (Enum.filter (function (`FieldType _| `ClassMember _) -> true | _ -> false) (DQ.enum g)) in

    (* Append to trace, TODO: found_visible/found_replaceable *)
    let trace = DQ.snoc state.trace g in
    (* History and suffix of searched path 
           i.e. path[last[h']] ++ q' == q
    *)
    let (history, q') = find_prefix (state.history, q) in
    BatLog.logf "Suffix %s\n" (Path.show q') ;
        
    (* Create the new search task *)
    let new_p = List.of_enum (Enum.filter_map (function (`ClassMember x | `FieldType x) -> Some {ident={txt=x;loc=none};subscripts=[]} | _ -> None) (DQ.enum q')) in    
    let current_path = path_of_history history in
    let new_state = {state with current_path;history;trace} in

    (* Merge all flat attributes from a pointer *)
    let merge_state state found_state =
      let (|||) fst = function Some x -> Some x | None -> fst in
      
      (* TODO: merge trace here? *)
      {state with replaceable = state.replaceable or found_state.replaceable ;
                  current_attr = {fa_var = state.current_attr.fa_var ||| found_state.current_attr.fa_var ;
                                  fa_cau = state.current_attr.fa_cau ||| found_state.current_attr.fa_cau ;
                                  fa_con = state.current_attr.fa_con ||| found_state.current_attr.fa_con ;
                                  fa_sort = state.current_attr.fa_sort ||| found_state.current_attr.fa_sort ;}
      }
    in
    
    begin match lookup_continue_or_yield new_state new_p with
        Success {lookup_success_value;lookup_success_state=found_state} -> helper (merge_state state found_state) lookup_success_value
      | r -> r
    end
    
  (* Replaceable/Constr means to look into it *)
  | Replaceable v -> helper {state with replaceable = true} v
  | Constr {constr=Cau c; arg} -> helper {state with current_attr = {state.current_attr with fa_cau = Some c}} arg
  | Constr {constr=Con c; arg} -> helper {state with current_attr = {state.current_attr with fa_con = Some c}} arg
  | Constr {constr=Var v; arg} -> helper {state with current_attr = {state.current_attr with fa_var = Some v}} arg
  | Constr {constr=Sort s; arg} -> helper {state with current_attr = {state.current_attr with fa_sort = Some s}} arg
  | Enumeration flds ->
    begin match p with
        [] -> Success {lookup_success_state=finish_component state; lookup_success_value=Enumeration flds}
      | [x] when StrSet.mem x.ident.txt flds ->
        let state = {(finish_component state) with current_ref = DQ.snoc state.current_ref {kind=CK_BuiltinAttr; component=x}} in
        Success {lookup_success_state=state;
                 lookup_success_value=Enumeration flds} 
      | _ -> Error {lookup_error_todo=p; lookup_error_state=state}
    end
  | (Int | Real | String | Bool) as v ->
    let rest = DQ.of_enum (List.enum (List.map (fun component -> {kind=CK_BuiltinAttr; component}) p)) in    
    let state = finish_component state in
    let lookup_success_state = {state with current_ref = DQ.append state.current_ref rest} in
    Success {lookup_success_state; lookup_success_value=v}
                
  | v -> begin match p with
        [] -> Success {lookup_success_state=finish_component state; lookup_success_value=v}
      | _ -> Error {lookup_error_todo=p; lookup_error_state=state}
    end
  in
  helper state e

(** Start lookup with the given state *)
and lookup_continue state x xs =
  match DQ.rear state.history with
    None -> raise EmptyScopeHistory
  | Some(ys,y) ->
    get_class_element_os state y.entry_structure x xs

and lookup_continue_or_yield state = function
    [] ->
    begin match DQ.rear state.history with
        None -> raise EmptyScopeHistory
      | Some(_,y) ->
        Success {lookup_success_state=state; lookup_success_value=Class y.entry_structure}
    end
    | x::xs -> lookup_continue state x xs

let rec forward state k c (todo:Path.t) =
  let current_path = DQ.snoc state.current_path (k :> Path.elem_t) in
  let state = {state with current_path} in
  match c with
  (* always append history, even if todo is empty *)
    Class (os) ->
    let history = append_to_history state k os in
    forward_os {state with history} os todo
  | c -> begin
      match DQ.front todo with
        None -> state
      | Some(x,xs) ->
        raise (ExpansionException ("expected a class. got: " ^ (show_class_value c)))
    end

and forward_os state {public;protected} todo =
  match DQ.front todo with
    None -> state
  | Some(`Protected, xs) -> forward_elements
                              {state with current_path = Path.snoc state.current_path `Protected} protected xs
  | _ -> forward_elements state public todo

and forward_elements state ({class_members; super; fields} as es) (todo:Path.t) =
  match DQ.front todo with
  | None -> raise (ExpansionException "Unexpected end-of-path")
  | Some(`FieldType x, xs) when StrMap.mem x fields ->
    forward state (`FieldType x) (StrMap.find x fields).field_class xs
      
  | Some(`ClassMember x, xs) when StrMap.mem x class_members ->
    forward state (`ClassMember x) (StrMap.find x class_members).class_ xs
      
  | Some(`SuperClass i, xs) when IntMap.mem i super ->
    forward state (`SuperClass i) (IntMap.find i super).class_  xs

  | Some (x, _) ->
    BatLog.logf "Fowarding failed. No element %s in %s" (Path.show_elem_t x) (Path.show state.current_path) ;
    raise (ForwardFailure x)

  | Some (`Protected, xs) -> raise (IllegalPath "protected")

(** Forward a lookup state by an (existing) (relative) pointer *)
let forward_state state todo = 
  match DQ.rear state.history with
    None -> raise EmptyScopeHistory
  | Some(_,y) ->
    forward_os state y.entry_structure todo

(** Start lookup with the given state, follow lexical scoping rules *)
let rec lookup_lexical_in state x xs =
  match DQ.rear state.history with
    None -> raise EmptyScopeHistory
  | Some(ys,y) ->
    match get_class_element_os state y.entry_structure x xs with
      Error {lookup_error_state={current_ref}} when current_ref==state.current_ref ->
      (* Found nothing, climb up scope *)
      lookup_lexical_in {(state_of_history ys) with current_scope=state.current_scope+1} x xs
    | r -> r

(** Create a lookup state from a normalized signature (i.e. root class) *)
let state_of_lib lib =
  {history = DQ.singleton {entry_structure = {empty_object_struct with public = lib}; entry_kind = `ClassMember ""};
   replaceable=false;
   trace = DQ.empty ;
   current_ref = DQ.empty;
   current_attr = no_attributes;
   current_scope = 0;
   current_path = DQ.empty}  

let lookup o p =
  let open Normalized in
  let state = state_of_lib o in
  match p with
    [] -> Success {lookup_success_value = Class {empty_object_struct with public = o};
                   lookup_success_state = state} ;
  | x::xs ->    
    lookup_lexical_in state x xs

