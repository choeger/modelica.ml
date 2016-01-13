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
open Normalized

exception EmptyName

let rec get_class_element_in global current_path {Normalized.class_members; super; fields} x xs =
  if StrMap.mem x class_members then begin
    let found = (DQ.snoc current_path (`ClassMember x)) in
    let r = (get_class_element global found (StrMap.find x class_members).class_ xs) in
    match r with
      `NothingFound -> (`PrefixFound {not_found=xs; found})      
    | r -> r
  end
  else if StrMap.mem x fields then begin
    let found = (DQ.snoc current_path (`FieldType x)) in
    let r = (get_class_element global found (StrMap.find x fields).field_class xs) in
    match r with
      `NothingFound -> (`PrefixFound {not_found=xs; found})      
    | r -> r
  end
  else (
    pickfirst_class global current_path (DQ.cons x xs) (IntMap.bindings super) )

and get_class_element_os global found_path {public;protected} x xs =
  let f = get_class_element_in global found_path public x xs in
  match f with
    `NothingFound -> get_class_element_in global (DQ.snoc found_path `Protected) protected x xs
  | _ as r -> r

and pickfirst_class global current_path name = function
    [] -> `NothingFound
  | (k,v)::vs ->
    let next_path = DQ.snoc current_path (`SuperClass k) in
    let f = get_class_element global next_path v.class_ name in
    begin match f with
        `NothingFound -> pickfirst_class global current_path name vs
      | r -> r
    end

and get_class_element global found_path e p =
  let open Normalized in 

  match DQ.front p with

  (* Empty name, we are done *)
    None ->
    let found_replaceable = match e with
        Replaceable _ -> true
      | _ -> false
    in
    `Found {found_path ; found_value = e;
            found_visible=true; found_replaceable}

  | Some (x, xs) -> begin
      match e with
      | Class os -> get_class_element_os global found_path os x xs

      (* we might encounter recursive elements *)
      | Recursive rec_term -> `Recursion {rec_term; search_state={found = found_path; not_found = p}}

      (* follow global references through self to implement redeclarations *)
      | GlobalReference g ->
        begin match DQ.front g with
            Some(x,xs) ->
            begin match follow_path_es global DQ.empty global xs x with
              | `Found {found_value} -> get_class_element global found_path found_value p
              | `Recursion _ as r -> r
              | `NothingFound | `PrefixFound _ as result -> BatLog.logf "Could not follow (probably recursive) %s\n" (show_class_path g); result
            end
          | None -> raise EmptyName
        end

      (* Replaceable/Constr means to look into it *)
      | Replaceable v -> get_class_element global found_path v p    
      | Constr {arg} -> get_class_element global found_path arg p
      | _ -> `NothingFound
    end    

let lookup o p =
  let open Normalized in
  match DQ.front p with
    None -> (`Found {found_value = Class {empty_object_struct with public = o}; found_path = DQ.empty; found_visible=true; found_replaceable=false}) ;
  | Some(x,xs) -> get_class_element_in o DQ.empty o x xs

