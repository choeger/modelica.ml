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

val nl : 'a -> 'a Location.loc

val int : int -> Syntax.exp
(** Constructor for integer literals *)
                   
val real : float -> Syntax.exp
val ide : string -> Syntax.exp
val bool : bool -> Syntax.exp
val string : string -> Syntax.exp
val colon : Syntax.exp
val end_ : Syntax.exp
val pow : Syntax.binary_exp -> Syntax.exp
val dpow : Syntax.binary_exp -> Syntax.exp
val mul : Syntax.binary_exp -> Syntax.exp
val dmul : Syntax.binary_exp -> Syntax.exp
val div : Syntax.binary_exp -> Syntax.exp
val ddiv : Syntax.binary_exp -> Syntax.exp
val plus : Syntax.binary_exp -> Syntax.exp
val dplus : Syntax.binary_exp -> Syntax.exp
val minus : Syntax.binary_exp -> Syntax.exp
val dminus : Syntax.binary_exp -> Syntax.exp
val uminus : Syntax.exp -> Syntax.exp
val uplus : Syntax.exp -> Syntax.exp
val udminus : Syntax.exp -> Syntax.exp
val udplus : Syntax.exp -> Syntax.exp
val gt : Syntax.binary_exp -> Syntax.exp
val lt : Syntax.binary_exp -> Syntax.exp
val leq : Syntax.binary_exp -> Syntax.exp
val geq : Syntax.binary_exp -> Syntax.exp
val neq : Syntax.binary_exp -> Syntax.exp
val eq_ : Syntax.binary_exp -> Syntax.exp
val and_ : Syntax.binary_exp -> Syntax.exp
val or_ : Syntax.binary_exp -> Syntax.exp
val not_ : Syntax.exp -> Syntax.exp
val if_ : Syntax.if_expression -> Syntax.exp
val range : Syntax.range -> Syntax.exp
val compr : Syntax.comprehension -> Syntax.exp
val array : Syntax.exp list -> Syntax.exp
val marray : Syntax.exp list list -> Syntax.exp
val explicitclosure : Syntax.exp -> Syntax.exp
val outputexpression : Syntax.exp option list -> Syntax.exp
val cr : Syntax.component list -> Syntax.component_reference
val cre : Syntax.component_reference -> Syntax.exp
val der : Syntax.exp
val initial : Syntax.exp
val assert_ : Syntax.exp
val any : string -> Syntax.component

val app : component_reference -> (string * exp) list -> exp

val known_component :
  ?known_type:flat_type -> Syntax.component_kind -> string -> Syntax.known_component
val cclass : ?known_type:flat_type -> string -> Syntax.known_component
val cvar : ?known_type:flat_type -> string -> Syntax.known_component
val cattr : ?known_type:flat_type -> string -> Syntax.known_component
val cconstfld : ?known_type:flat_type -> string -> Syntax.known_component
val cfld : ?known_type:flat_type -> string -> Syntax.known_component
val cfunc : ?known_type:flat_type -> string -> Syntax.known_component
val cbuiltinfun : ?known_type:flat_type -> string -> Syntax.known_component
val cbuiltinclass : ?known_type:flat_type -> string -> Syntax.known_component
val knownref : int -> Syntax.known_component list -> Syntax.component_reference
val rootref :  Syntax.known_component list -> Syntax.component_reference
val unknownref : string list -> Syntax.component_reference
val time : Syntax.known_component

val empty_app : component_reference -> application
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
*)

val root_type : string list -> texp
(** Create a root-type-name from the list of its elements 
*)

(** Empty operator record description *)
val empty_or : operator_record

(** Flat-type argument *)
val ftarg : string -> ?ftarg_opt:bool -> flat_type -> ftarg  
