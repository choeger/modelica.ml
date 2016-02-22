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
open Syntax_fragments
open Normalized
    
exception EmptyName
exception ExpansionException of string
exception ForwardFailure of Path.elem_t
exception EmptyScopeHistory
exception HierarchyError
exception DecompressionError
  
type trace_t = Path.t DQ.t [@@deriving show,yojson]

type lnode = { up : lnode option; tip : lclass }

and lclass = { clup : lnode option; clbdy : object_struct; }
  [@@deriving show,yojson]

type lookup_value = LClass of lclass | LPrimitive of class_value
  [@@deriving show,yojson]

let class_value_of_lookup = function LClass {clbdy} -> Class clbdy | LPrimitive cv -> cv

let map_lv f = function LClass {clup; clbdy} -> LClass {clup; clbdy}
                      | LPrimitive v -> LPrimitive (f v)

type lookup_state = {
  self : lnode ;
  trace : trace_t; (** The found references *)
  current_path : Path.t ; (** The path to the current class value *)
  current_attr : flat_attributes ;
  current_ref : Syntax.known_ref; (** The search request as a resolved component *)
  current_scope : int; (** Relative current scope *)
} [@@deriving show,yojson]

let rec root_class_of self = match self.up with None -> self.tip | Some self -> root_class_of self

let empty_lookup_state = {trace=DQ.empty; self={up=None;tip={clup=None; clbdy=empty_object_struct}};
                          current_path=Path.empty;
                          current_attr=no_attributes; current_ref=DQ.empty; current_scope=0}

let dump_lookup_state {current_path} = Printf.sprintf "Last class: %s\n" (Path.show current_path)

type lookup_success_struct = { lookup_success_state : lookup_state ;
                               lookup_success_value : lookup_value ;
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


(** wrap a scope of visited classes into a new lookup state *)
let state_of_self self = {self;
                          trace = DQ.empty ;
                          current_ref = DQ.empty;
                          current_attr = no_attributes;
                          current_scope = 0;
                          current_path = self.tip.clbdy.source_path}

let undefined x {Normalized.class_members; super; fields} =
  let not_inherited _ v b = b && (match v.super_shape with Shape flds -> not (StrMap.mem x flds) | _ -> true) in
  not (StrMap.mem x class_members) && not (StrMap.mem x fields) && (IntMap.fold not_inherited super true)

let rec get_class_element_in state {Normalized.class_members; super; fields} x xs =  
  if StrMap.mem x.ident.txt class_members then begin
    let current_ref = DQ.snoc state.current_ref {kind = CK_Class; component=x} in
    let cv = (StrMap.find x.ident.txt class_members).class_ in
    get_class_element {state with current_ref} (`ClassMember x.ident.txt) cv xs
  end
  else if StrMap.mem x.ident.txt fields then begin
    let current_ref = DQ.snoc state.current_ref {Syntax.kind = CK_Continuous; component=x} in
    get_class_element {state with current_ref} (`FieldType x.ident.txt) (StrMap.find x.ident.txt fields).field_class xs
  end
  else begin
    (pickfirst_class state x xs (IntMap.bindings super) )
  end
  
and get_class_element_os state ({public;protected} as os) x xs =
  let f = get_class_element_in state public x xs in
  match f with
    Error {lookup_error_state={current_ref}} when undefined x.ident.txt public ->
    (* Nothing found, search protected section *)
    let current_path = DQ.snoc state.current_path `Protected in
    get_class_element_in {state with current_path} protected x xs
  | _ as r -> r (* Something found *)

and pickfirst_class state x xs = function
    [] -> Error {lookup_error_state=state; lookup_error_todo=x::xs}
  | (k,v)::vs ->
    begin
      match v.super_shape with
      | Primitive ->
        let current_ref = DQ.append state.current_ref (DQ.of_list (List.map (fun component -> {kind=CK_BuiltinAttr;component}) (x::xs))) in
        Success {lookup_success_state={state with current_ref}; lookup_success_value=LPrimitive Unit}
      | Shape shape when StrMap.mem x.ident.txt shape ->
        (* Always re-evaluate the super class to catch all redeclarations *)
        let super = get_class_element state (`SuperClass k) v.super_type [] in
        begin match super with
          | Success {lookup_success_state; lookup_success_value=LClass {clup;clbdy}} ->
            let super_state = {state with self={state.self with up=clup};
                                          current_path = DQ.snoc state.current_path (`SuperClass k);
                              } in
            get_class_element_os super_state clbdy x xs
            
        | Success {lookup_success_state; lookup_success_value} ->
            raise (Failure ("Lookup of " ^ x.ident.txt ^ "in a non-structured type"))
        | (Error _ | Recursion _) as e -> e
        end
      | Shape _ -> pickfirst_class state x xs vs
    end

(**
  $state : lookup state 
  $k : kind of this class value
  $p : components todo
*)
and get_class_element state k e p =  
  let open Normalized in
  (match p with
    [{ident={txt="im"}}] ->
    BatLog.logf "Looking for im in %s\n" (show_class_value e)
  |  _ -> ());
    
  let current_path = Path.snoc state.current_path k in
  let state = {state with current_path} in
  
  let finish_component state = match DQ.rear state.current_ref with    
    (* update last component reference with collected flat attribute *)
      None
    | Some (_,{kind=CK_Class}) -> state
    | Some(xs, x) -> {state with current_ref = (DQ.snoc xs {x with kind=ck_of_var state.current_attr.fa_var})}
  in

  let project state v =
    let state = {(finish_component state) with current_path} in
    function
      [] ->
      let lookup_success_value = map_lv (fun sval ->
          let {flat_attr; flat_val} = merge_attributes state.current_attr sval in
          unflat {flat_val;flat_attr}) v       
      in
      Success {lookup_success_state=state;lookup_success_value}
    | x::xs ->      
      begin match v with
          LClass {clbdy} -> get_class_element_os state clbdy x xs                              
        | LPrimitive cv ->
          begin match cv with
            | Int | Real | String | Bool ->
              let rest = DQ.of_list (List.map (fun component -> {kind=CK_BuiltinAttr; component}) (x::xs)) in
              let lookup_success_state = {state with current_ref = DQ.append state.current_ref rest} in
              let flat = merge_attributes state.current_attr cv in
              Success {lookup_success_state;
                       lookup_success_value=LPrimitive (unflat flat)} 
            | Enumeration flds ->
              begin match x with                  
                | {ident={txt="start" | "min" | "max" | "fixed" | "quantity"}} as x when xs = [] ->
                  let lookup_success_state = {state with current_ref = DQ.snoc state.current_ref {kind=CK_BuiltinAttr; component=x}} in
                  let flat = merge_attributes state.current_attr cv in
                  Success {lookup_success_state;
                           lookup_success_value=LPrimitive (unflat flat)} 
        
                | x when StrSet.mem x.ident.txt flds && xs = [] ->
                  let lookup_success_state = {state with current_ref = DQ.snoc state.current_ref {kind=CK_BuiltinAttr; component=x}} in
                  let flat = merge_attributes state.current_attr cv in
                  Success {lookup_success_state;
                           lookup_success_value=LPrimitive (unflat flat)} 
                | _ -> Error {lookup_error_todo=p; lookup_error_state=state}
              end
            | _ -> raise (Failure ("Such builtins should not occur here (" ^ x.ident.txt ^ ")") )
          end
      end
  in
  
  let rec helper state = function
  | Class os ->
    assert (not (Path.equal os.source_path state.self.tip.clbdy.source_path)) ;
    let tip = {clup = Some state.self; clbdy = os} in
    let self =  {up = tip.clup; tip} in
    let lv = LClass tip in    
    project {state with self} lv p

  (* we might encounter recursive elements *)
  | Recursive lookup_recursion_term -> Recursion {lookup_recursion_term;
                                                  lookup_recursion_state=state;
                                                  lookup_recursion_todo=p}

    (* follow dynamic references through self to implement redeclarations *)
  | DynamicReference {upref; downref} ->
    let rec upwards self = function
        0 -> {self with up = self.tip.clup}
      | n -> begin match self.up with None -> raise HierarchyError
                                    | Some up -> upwards up (n-1)
        end
    in
    let self = upwards state.self upref in
    let state = {state with self} in
    begin match DQ.front downref with
        None ->
        project state (LClass self.tip) p
      | Some (y,ys) ->
        begin
        (* Evaluate dynamic reference: back to tip, open recursion *)
          match get_class_element_os state state.self.tip.clbdy (any y) (List.map any (Name.to_list ys)) with
            Success success ->
            (* Continue search *)
            let  {self; current_attr} = success.lookup_success_state in
            project {state with self; current_attr} success.lookup_success_value p
          | e -> e
        end
    end

  | GlobalReference g ->
    begin match Name.front (Name.of_ptr g) with
      Some(x,xs) ->
        let root = root_class_of state.self in
        let state = {state with self={up=None; tip=root}} in
        begin match get_class_element_os state root.clbdy (any x) (List.map any (Name.to_list xs)) with
        Success success ->
            (* Continue search *)
            project {state with self = success.lookup_success_state.self} success.lookup_success_value p
          | e -> e
        end
      | None -> raise EmptyName
    end
    
  (* Replaceable/Constr means to look into it *)
  | Replaceable v -> helper {state with current_attr = {state.current_attr with fa_replaceable=true}} v
  | Constr {constr=Cau c; arg} -> helper {state with current_attr = {state.current_attr with fa_cau = Some c}} arg
  | Constr {constr=Con c; arg} -> helper {state with current_attr = {state.current_attr with fa_con = Some c}} arg
  | Constr {constr=Var v; arg} -> helper {state with current_attr = {state.current_attr with fa_var = Some v}} arg
  | Constr {constr=Sort s; arg} -> helper {state with current_attr = {state.current_attr with fa_sort = Some s}} arg
                                     
  | v -> project state (LPrimitive v) p
  in
  helper state e

(** Start lookup with the given state *)
and lookup_continue state x xs =
  get_class_element_os state state.self.tip.clbdy x xs

and lookup_continue_or_yield state = function
    [] ->
    Success {lookup_success_state=state; lookup_success_value=LClass state.self.tip}
    | x::xs -> lookup_continue state x xs

let rec forward state k c (todo:Path.t) =
  let current_path = DQ.snoc state.current_path (k :> Path.elem_t) in
  let state = {state with current_path} in
  match c with
  (* always append history, even if todo is empty *)
    (Replaceable (Class os) | Class (os)) ->
    let self = {tip = {clup=Some state.self; clbdy=os}; up=Some state.self} in
    forward_os {state with self} os todo
  | c -> begin
      match DQ.front todo with
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
    raise (ExpansionException ("Cannot forward into a superclass: " ^ (Path.show state.current_path)))

  | Some (x, _) ->
    BatLog.logf "Fowarding failed. No element %s in %s" (Path.show_elem_t x) (Path.show state.current_path) ;
    raise (ForwardFailure x)

  | Some (`Protected, xs) -> raise (IllegalPath "protected")

(** Forward a lookup state by an (existing) (relative) pointer *)
let forward_state state todo = 
  forward_os state state.self.tip.clbdy todo

(** Start lookup with the given state, follow lexical scoping rules *)
let rec lookup_lexical_in state x xs =
  if undefined x.ident.txt state.self.tip.clbdy.public &&
     undefined x.ident.txt state.self.tip.clbdy.protected then
    (* Found nothing, climb up scope *)
    begin match state.self.up with
        None -> Error {lookup_error_state=state; lookup_error_todo=x::xs}
      | Some self -> lookup_lexical_in {state with self;current_scope=state.current_scope+1} x xs
    end
  else begin
    get_class_element_os state state.self.tip.clbdy x xs
  end
(** Create a lookup state from a normalized signature (i.e. root class) *)
let state_of_lib lib =
  {self={tip={clup=None; clbdy={empty_object_struct with public=lib}};up=None};
   trace = DQ.empty ;
   current_ref = DQ.empty;
   current_attr = no_attributes;
   current_scope = 0;
   current_path = DQ.empty}

let lookup o p =
  let open Normalized in
  let state = state_of_lib o in
  match p with
    [] -> Success {lookup_success_value = LClass state.self.tip;
                   lookup_success_state = state} ;
  | x::xs ->    
    lookup_lexical_in state x xs

