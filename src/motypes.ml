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
 Modelica 3.x normalized types
 *)
module StdFormat = Format
open Batteries
module Format = StdFormat
open Utils
open Ast.Flags
module DS = Syntax

module Name = struct         
  type t = string DQ.t [@@deriving show, yojson]
                                                                                        
  let str_compare a b = String.compare a b 

  let compare a b = Enum.compare str_compare (DQ.enum a) (DQ.enum b)
                                 
  let hash = Hashtbl.hash
               
  let equal a b = compare a b = 0
                                  
  let empty = DQ.empty

  let is_empty = DQ.is_empty
                
  let of_list = DQ.of_list

  let singleton = DQ.singleton
                  
  let rec scope_of_ptr_ tmp dq = match DQ.front dq with
    | None -> tmp
    | Some ((`Field _ | `Any _ | `SuperClass _ ), _) -> tmp
    | Some (`Protected, r) -> scope_of_ptr_ tmp r
    | Some ((`ClassMember x), r) -> scope_of_ptr_ (DQ.snoc tmp x) r

  let scope_of_ptr dq = match (DQ.rear dq) with
      Some(xs,`ClassMember x) -> (scope_of_ptr_ DQ.empty xs)
    | _ -> (scope_of_ptr_ DQ.empty dq)
                  
  let rec of_ptr_ tmp dq = match DQ.front dq with
    | None -> tmp
    | Some ((`SuperClass _  | `Protected), r) -> of_ptr_ tmp r
    | Some ((`ClassMember x | `Field x | `Any x), r) -> of_ptr_ (DQ.snoc tmp x) r
                  
  let of_ptr dq = of_ptr_ DQ.empty dq
                                                                        
end

module NameMap = Map.Make(Name)
              
type constr =  CArray of int
             | CSort of sort
             | CRepl
             | CVar of variability
             | CCau of causality
             | CCon of connectivity
             | CDer of string list
                         [@@deriving yojson,eq,show]

type class_path_elem = [`Protected | `ClassMember of string | `Field of string | `SuperClass of int] [@@deriving eq,show,yojson]

type class_path = class_path_elem DQ.t [@@deriving eq,show,yojson]
                                                                                                     
type class_ptr_elem = [class_path_elem | `Any of string] [@@deriving eq,show,yojson]

type class_ptr = class_ptr_elem DQ.t [@@deriving eq,show,yojson]
                         
type class_term = Reference of DS.name
                | RedeclareExtends
                | Empty of open_class
                | Close
                | RootReference of DS.name
                | PInt | PReal | PString | PBool | PExternalObject
                | PEnumeration of StrSet.t
                | Constr of class_constr
                | Delay of class_term
                    [@@deriving yojson,eq,show]

and open_class = { class_sort : sort ; class_name : Name.t }
                    
and  class_constr = { constr : constr ; arg : class_term }
                      
type class_stmt = {lhs : class_ptr ; rhs : class_term} [@@deriving eq,show,yojson]
                                                       
type class_program = class_stmt list [@@deriving show,yojson]
      
module Normalized = struct
    
    type constr =  Array of int
                 | Sort of sort
                 | Var of variability
                 | Cau of causality
                 | Con of connectivity
                 | Der of string list
                                 [@@deriving yojson,show,eq]                                 

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
                       | GlobalReference of Name.t
                       | Recursive of rec_term
                                        [@@deriving eq,show,yojson]

     and rec_term = { rec_lhs : class_path; rec_rhs : class_term }
                                        
     and constr_value = { arg : class_value ; constr : constr }
                                 
     and object_struct = { object_sort : sort ;
                           source_name : Name.t;
                           public : elements_struct [@default {class_members = StrMap.empty; super = IntMap.empty; fields = StrMap.empty }];
                           protected : elements_struct [@default {class_members = StrMap.empty; super = IntMap.empty; fields = StrMap.empty }]}
                                                                 
     and elements_struct = { class_members : class_value StrMap.t [@default StrMap.empty];
                             super : class_value IntMap.t [@default IntMap.empty];
                             fields : class_value StrMap.t [@default StrMap.empty] }
                             

    let empty_elements = {class_members = StrMap.empty; super = IntMap.empty; fields = StrMap.empty }
    let empty_object_struct = {object_sort=Class; source_name=Name.empty; public=empty_elements; protected=empty_elements}

    let empty_class = Class empty_object_struct 

    let rec compress = function
        Class os -> Class {os with public = compress_elements os.public; protected = compress_elements os.protected }
      | Constr {constr; arg} -> Constr {constr; arg = compress arg}
      | Replaceable v -> Replaceable (compress v)
      | v -> v
               
    and compress_elements es = {es with fields = StrMap.map pack_class es.fields; super = IntMap.map pack_class es.super; class_members = StrMap.map compress es.class_members }

    and pack_class = function
        Class os -> GlobalReference os.source_name
      | Constr {constr; arg} -> Constr {constr; arg = pack_class arg}
      | Replaceable v -> Replaceable (pack_class v)
      | v -> v
  end
                                                                                           

                                                                                   

