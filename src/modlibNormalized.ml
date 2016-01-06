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

(**
   Modelica 3.x normalized library
*)

open Batteries
open Utils
open Syntax
open Flags

open ModlibInter

type constr = Array of int
            | Sort of sort
            | Var of variability
            | Cau of causality
            | Con of connectivity
            | Der of string list
                  [@@deriving eq,yojson,show]                                 

let norm_constr = function
    CArray i -> Array i
  | CSort s -> Sort s
  | CVar v -> Var v
  | CCau c -> Cau c
  | CCon c -> Con c
  | CDer d -> Der d
  | CRepl -> raise (Invalid_argument "'replaceable' is not a normlized constructor")

type class_value = Int | Real | String | Bool | Unit | ProtoExternalObject
                 | Enumeration of StrSet.t
                 | Constr of constr_value
                 | Class of object_struct
                 | Replaceable of class_value
                 | GlobalReference of class_path
                 | Recursive of rec_term
                 | DynamicReference of class_path
  [@@deriving eq,show,yojson,folder,mapper]

and rec_term = { rec_lhs : class_path; rec_rhs : class_term }

and constr_value = { arg : class_value ; constr : constr }

and object_struct = { object_sort : sort ;
                      source_path : Path.t ;
                      public : elements_struct [@default {class_members = StrMap.empty; super = IntMap.empty; fields = StrMap.empty }];
                      protected : elements_struct [@default {class_members = StrMap.empty; super = IntMap.empty; fields = StrMap.empty }] ;
                      behavior : behavior [@default {algorithms=[]; equations=[]; initial_algorithms=[]; initial_equations=[]; external_=None}] ;
                    }

and field_modification = Modify of exp
                       | Nested of field_modification StrMap.t

and class_field = { field_class : class_value ;
                    field_binding : exp option [@default None] ;
                    field_mod : field_modification StrMap.t [@default StrMap.empty]}

and class_member = { class_ : class_value ;
                     class_mod : field_modification StrMap.t [@default StrMap.empty]}

and elements_struct = { class_members : class_member StrMap.t [@default StrMap.empty];
                        super : class_value IntMap.t [@default IntMap.empty];
                        fields : class_field StrMap.t [@default StrMap.empty]
                      }

type flat_attributes = {
  fa_sort : sort option [@default None] ;
  fa_var : variability option [@default None];
  fa_con : connectivity option [@default None];
  fa_cau : causality option [@default None];
}	[@@deriving show,yojson]		     

type flat_repr = {
  flat_val : class_value ;
  flat_attr : flat_attributes [@default {fa_sort=None;fa_var=None;fa_con=None;fa_cau=None}]
} [@@deriving show,yojson]

let rec flat_ fa = function
  | Constr {arg; constr = Var v} when fa.fa_var = None -> flat_ {fa with fa_var = Some v} arg
  | Constr {arg; constr = Con c} when fa.fa_con = None -> flat_ {fa with fa_con = Some c} arg
  | Constr {arg; constr = Cau c} when fa.fa_cau = None -> flat_ {fa with fa_cau = Some c} arg
  | Constr {arg; constr = Sort s} when fa.fa_sort = None -> flat_ {fa with fa_sort = Some s} arg
  | Constr {arg; constr} -> flat_ fa arg
  | Replaceable cv -> begin match flat_ fa cv with
        {flat_val = Replaceable cv ; flat_attr } as fv -> fv
      | fv -> {fv with flat_val = Replaceable fv.flat_val}
    end
  | flat_val -> {flat_val; flat_attr = fa}  

let flat = flat_ {fa_con = None; fa_cau = None; fa_sort = None; fa_var = None}

let rec unflat = function
  | {flat_val = Replaceable flat_val} as fv -> Replaceable (unflat {fv with flat_val})
  | {flat_val; flat_attr={fa_sort;fa_var;fa_cau;fa_con}} ->
    let unflat_sort s cv = match s with None -> cv | Some s -> Constr {arg=cv; constr=Sort s} in
    let unflat_cau c cv = match c with None -> cv | Some c -> Constr {arg=cv; constr=Cau c} in
    let unflat_con c cv = match c with None -> cv | Some c -> Constr {arg=cv; constr=Con c} in
    let unflat_var v cv = match v with None -> cv | Some v -> Constr {arg=cv; constr=Var v} in
    flat_val |> (unflat_sort fa_sort) |> (unflat_var fa_var) |> (unflat_con fa_con) |> (unflat_cau fa_cau)

let norm_cv = flat %> unflat

let no_behavior = {algorithms=[]; equations=[]; initial_algorithms=[]; initial_equations=[]; external_=None}
let empty_elements = {class_members = StrMap.empty; super = IntMap.empty; fields = StrMap.empty }
let empty_object_struct = {object_sort=Class; source_path=Path.empty; public=empty_elements; protected=empty_elements; behavior=no_behavior}

let empty_class = Class empty_object_struct
let empty_class_member = {class_ = empty_class; class_mod = StrMap.empty}

type prefix_found_struct = { found : class_path ; not_found : Name.t } [@@deriving show,yojson]

let show_prefix_found {found; not_found} = "No element named " ^ (Name.show not_found) ^ " in " ^ (Name.show (Name.of_ptr found))

type found_struct = { found_path : class_path ; found_value : class_value ; found_visible : bool ; found_replaceable : bool } [@@deriving show,yojson]

type search_error = [ `NothingFound | `PrefixFound of prefix_found_struct ] [@@deriving show,yojson]

type found_recursion = { rec_term : rec_term ; search_state : prefix_found_struct } [@@deriving show,yojson]

type search_result = [`Found of found_struct | `Recursion of found_recursion | search_error ] [@@deriving show,yojson]

exception IllegalPath of string

let rec follow_path global found_path found_value path = match DQ.front path with
    None ->
    let found_replaceable = match found_value with
        Replaceable _ -> true
      | _ -> false
    in
    `Found {found_path; found_value; found_visible=true; found_replaceable}

  | Some (x,xs) -> begin
      match found_value with
      | Class os -> follow_path_os global found_path os xs x
      (* follow global references *)
      | GlobalReference g -> begin
          match DQ.front g with
            None -> raise (IllegalPath "")
          | Some (y,ys) -> begin 
              match follow_path_es global DQ.empty global ys y with
              | `Found {found_value} ->
                follow_path global found_path found_value path
              | `Recursion _ as r -> r
              | `NothingFound | `PrefixFound _ as result -> result
            end
        end
      (* Replaceable/Constr means to look into it *)
      | Replaceable v -> begin match follow_path global found_path v path with
            `Found fs -> `Found {fs with found_replaceable=true}
          | `Recursion _ as r -> r
          | `NothingFound | `PrefixFound _ as result -> result
        end
      | Constr {arg} -> follow_path global found_path arg path
      | _ -> `NothingFound
    end

and follow_path_os global found_path {protected; public} todo = function
    `Protected -> begin match DQ.front todo with
        None -> raise (IllegalPath "")
      | Some(x,xs) -> follow_path_es global found_path protected xs x
    end    
  | x -> follow_path_es global found_path public todo x

and follow_path_es global found_path {class_members;super;fields} todo = function
    `SuperClass n when IntMap.mem n super ->
    follow_path global (DQ.snoc found_path (`SuperClass n))
      (IntMap.find n super) todo

  | `SuperClass n -> raise (IllegalPath ("super(" ^ (string_of_int n) ^ ")"))

  | `FieldType x when StrMap.mem x fields ->
    follow_path global (DQ.snoc found_path (`FieldType x))
      (StrMap.find x fields).field_class todo

  | `FieldType x -> raise (IllegalPath x)

  | `ClassMember x when StrMap.mem x class_members ->
    follow_path global (DQ.snoc found_path (`ClassMember x))
      (StrMap.find x class_members).class_ todo

  | `ClassMember x -> raise (IllegalPath x)


let lookup_path global path = match DQ.front path with
    Some (x,xs) -> follow_path_es global DQ.empty global xs x
  | None -> raise (IllegalPath "")

exception CannotUpdate of string * string * string

let rec update_ (lhs:class_path) rhs ({class_members;fields;super} as elements) = match DQ.front lhs with
    None -> elements
  | Some (`SuperClass i, r) -> {elements with super = update_intmap r rhs i super} 
  | Some (`FieldType x, r) -> {elements with fields = update_field_map r rhs x fields}
  | Some (`ClassMember x, r) -> {elements with class_members = update_map r rhs x class_members}
  | Some (`Protected,_) -> raise (IllegalPath "")

and update_class_member lhs rhs ({class_} as cm) =
  {cm with class_ = update_class_value lhs rhs class_}

and update_map lhs rhs x m =  
  StrMap.modify_def empty_class_member x (update_class_member lhs rhs) m

and update_field_map lhs rhs x m =  
  StrMap.modify_def {field_class=empty_class;field_binding=None;field_mod=StrMap.empty}
    x (update_field_class_value lhs rhs) m

and update_field_class_value lhs rhs f = {f with field_class = update_class_value lhs rhs f.field_class}

and update_intmap lhs rhs i map =  
  IntMap.modify_def empty_class i (update_class_value lhs rhs) map

and update_class_value lhs rhs = function
  | Constr {constr; arg} -> Constr {constr ; arg = (update_class_value lhs rhs arg)}
  | Class ({public; protected} as os) -> begin match DQ.front lhs with
        None -> rhs
      | Some(`Protected, q) -> Class {os with protected = update_ q rhs protected}
      | Some _ -> Class {os with public = update_ lhs rhs public}
    end
  | Replaceable cv -> Replaceable (update_class_value lhs rhs cv)
  | (Recursive _ | Int | Real | String | Bool | Unit | ProtoExternalObject | Enumeration _ | GlobalReference _ | DynamicReference _) as v ->
    begin match DQ.front lhs with
        None -> rhs
      | Some (x,xs) -> raise (CannotUpdate(Path.show_elem_t x, show_class_path xs, show_class_value v))
    end

let update lhs rhs es = update_ lhs rhs es
