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

(** Intermediate representation of Modelica libraries *)

open Utils
open Syntax.Flags
module DS = Syntax

(** Class/Type constructors *)
type constr = CArray of int
            | CSort of sort
            | CRepl
            | CVar of variability
            | CCau of causality
            | CCon of connectivity
            | CDer of string list
                  [@@deriving eq,yojson,show]

module Path = struct
  (** Known part of a path to a element in the global class hierarchy *)
  type elem_t = [`Protected | `ClassMember of string | `FieldType of string | `SuperClass of int] [@@deriving eq,ord,show,yojson]

  (** Path to a element in the global class hierarchy *)
  type t = elem_t DQ.t [@@deriving eq,ord,show,yojson]

  let append = DQ.append

  let snoc = DQ.snoc

  let cons = DQ.cons
  
  let rear = DQ.rear

  let front = DQ.front
  
  let empty : t = DQ.empty

  let of_list = DQ.of_list
  
  let singleton : elem_t -> t = DQ.singleton

  let size = DQ.size
  
  let cm x = `ClassMember x  
end

type class_path = Path.t [@@deriving eq,show,yojson]

module PathMap = Map.Make (Path)

(** Part of a path to a element in the global class hierarchy, including parts of unknown kind *)
type class_ptr_elem = [Path.elem_t | `Any of string] [@@deriving eq,show,yojson]

(** Path to a element in the global class hierarchy (including possibly unknown elements) *)
type class_ptr = class_ptr_elem DQ.t [@@deriving eq,show,yojson]

type field_property = { fld_name : string; fld_pos : int; fld_defined : bool } [@@deriving eq,yojson,show]

(** Intermediate language to describe classes/types *)
type class_term = Reference of DS.name
                | RedeclareExtends
                | Empty of open_class
                | Close of field_property list
                | RootReference of DS.name
                | KnownPtr of class_ptr
                | PInt | PReal | PString | PBool | PExternalObject
                | PEnumeration of StrSet.t
                | Constr of class_constr
                    [@@deriving eq,yojson,show]

and open_class = { class_sort : sort ; class_name : Name.t }

and  class_constr = { constr : constr ; arg : class_term }

type ('lhs, 'rhs) stmt = {lhs : 'lhs ; rhs : 'rhs} [@@deriving show,yojson]

(** Assignment of a class/type in the global hierachy *)
type class_stmt = (class_ptr, class_term) stmt [@@deriving show,yojson]

(** Path to a term in the global hierarchy *)
type value_ptr = { scope : class_ptr ; field : Syntax.components } [@@deriving eq,show,yojson]

(** Assignment of term in the global hierachy *)
type value_stmt = (value_ptr, Syntax.exp) stmt [@@deriving show,yojson]


(** Payload storage *)
type payload_stmt = (class_ptr, Syntax.behavior Syntax.annotated) stmt [@@deriving show,yojson]

type class_program = class_stmt list [@@deriving show,yojson]

type value_program = value_stmt list [@@deriving show,yojson]
