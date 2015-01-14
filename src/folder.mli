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

(** {2 A generic Syntax folder inspired by OCaml's Ast_mapper } *)

open Syntax

type ('s, 'a) fold_method = ('a folder) -> 's -> 'a -> 'a
(** A fold-method works by open recursion on a folder record.
    It takes the to-be-folded sort and a value as input and yields
    a new value *)
                                                         
and 'a folder = {
  fold_unit_ : (unit_,'a) fold_method;
  fold_within : (name option,'a) fold_method;
  fold_comment : (comment,'a) fold_method;
  fold_annotation : (modification,'a) fold_method;
  fold_typedef_options : (typedef_options,'a) fold_method;
  fold_typedef : (typedef,'a) fold_method;
  fold_composition : (composition,'a) fold_method;
  fold_redeclared_typedef : (typedef,'a) fold_method;
  fold_extension : (extension,'a) fold_method;
  fold_def : (definition,'a) fold_method;
  fold_redeclared_def : (definition,'a) fold_method;
  fold_import : (import,'a) fold_method;
  fold_import_desc : (import_desc,'a) fold_method;
  fold_imports : (import list,'a) fold_method;
  fold_public : (elements,'a) fold_method;
  fold_protected : (elements,'a) fold_method;
  fold_cargo : (behavior,'a) fold_method;
  fold_constraint_ : (constraint_,'a) fold_method;
  fold_der_spec : (der_spec,'a) fold_method;
  fold_enum_literal : (enum_literal,'a) fold_method;
  fold_algorithm : (algorithm,'a) fold_method;
  fold_external_def : (external_def,'a) fold_method;
  fold_texp : (texp,'a) fold_method;
  fold_exp : (exp,'a) fold_method;
  fold_idx : (idx,'a) fold_method;
  fold_statement_desc : (statement_desc,'a) fold_method;
  fold_statement : (statement,'a) fold_method;
  fold_equation_desc : (equation_desc,'a) fold_method;
  fold_equation : (equation,'a) fold_method;
  fold_modification : (modification,'a) fold_method;
  fold_type_redeclaration : (type_redeclaration,'a) fold_method;
  fold_component_redeclaration : (component_redeclaration,'a) fold_method;
  fold_component_modification : (component_modification,'a) fold_method;
  fold_component_modification_struct : (component_modification_struct,'a) fold_method;
  fold_modification_value : (modification_value,'a) fold_method;
  fold_name : (name,'a) fold_method;
  fold_named_arg : (named_arg,'a) fold_method;
  fold_identifier : (string,'a) fold_method;
  fold_comment_str : (string,'a) fold_method;
  fold_location : (Location.t,'a) fold_method;                              
 }  
(** A folder record implements one "method" per syntactic category,
    using an open recursion style: each method takes as its first
    argument the folder to be applied to children in the syntax
    tree. *)


val fold_id : ('sort,'a) fold_method
(** Dummy fold method, returns the input *)

val fold_commented : ('sort, 'a) fold_method -> ('sort commented, 'a) fold_method
(** Lift an element fold method over a commented element *)

val fold_located : ('sort, 'a) fold_method -> ('sort Location.loc, 'a) fold_method
(** Lift an element fold method over a located element *)

val fold_list : ('sort, 'a) fold_method -> ('sort list, 'a) fold_method
(** Lift an element fold method over a list of elements *)

val fold_option : ('sort, 'a) fold_method -> ('sort option, 'a) fold_method                                                           
(** Lift an element fold method over an optional elements *)

val fold_for_loop : ('sort, 'a) fold_method -> ('sort for_loop_struct, 'a) fold_method                                                           
(** Lift an element fold method over a loop structure containing this element as body *)

val fold_conditional : ('sort, 'a) fold_method -> ('sort condition_struct, 'a) fold_method                                                           
(** Lift an element fold method over a conditional structure containing this element as body *)

