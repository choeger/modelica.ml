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

(** Useful fragments of Modelica syntax *)

open Syntax

val empty_app : exp -> application
(** Return an empty application with the given expression as function *)

val named : string ->  exp -> named_arg
(** Convenience constructor for {!Syntax.named_arg} with no location information attached *)
                                      
val no_comment : comment
(** The empty comment *)

val unannotated : 'a -> 'a annotated
(** Combine any element with an empty annotation *)

val uncommented : 'a -> 'a commented
(** Combine any element with the empty comment *)

val no_modification : modification
(** The empty modification *)
                        
val no_def_options : definition_options
(** The options parsed from no definition flags *)

val empty_def : definition_structure
(** A skeleton for definitions *)
                       
val no_type_options : typedef_options
(** The options parsed from no type-definition flags *)

val empty_typedef : unit typedef_struct
(** A skeleton for type-definitions *)

val empty_behavior : behavior
(** The empty cargo section of a class *)
                        
val empty_elements : elements
(** The empty element list *)
                       
val empty_composition : composition
(** The empty composition *)
                          
exception EmptyName
(** Thrown when attempted to create a name or type-name from an empty list *)

val name : string list -> exp
(** Create a name from the list of its elements 
    @raise EmptyName in case of the empty list
*)

val type_name : string list -> texp
(** Create a type-name from the list of its elements 
    @raise EmptyName in case of the empty list
*)