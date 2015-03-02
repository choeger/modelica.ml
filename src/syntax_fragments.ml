
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
open Utils
       
let empty_app f = { fun_ = f ; args = [] ; named_args = [] }

let no_attr e = { term = e ; attr = () }
                    
let named x argument = {argument_name = Location.mknoloc x ; argument }
                    
let no_comment = { annotated_elem = None ; annotation = None }

let unannotated annotated_elem = { annotated_elem ; annotation = None }
                   
let uncommented a = { commented = a ; comment = no_comment }
                      
let no_modification = { types = [] ; components = [] ; modifications = [] }

let no_def_options = { final = false ; replaceable = false ; scope = Local }
                        
let empty_def  = { def_name ="" ; def_type = TName []; def_options = no_def_options ; def_constraint = None ; def_rhs = None ; def_if = None }

let no_type_options = { partial = false ; encapsulated = false ;
                        type_final = false ; type_replaceable = false ;}

let empty_typedef = { td_name = Location.mknoloc "" ; type_exp = () ; type_options = no_type_options ; cns = None ; sort = Type}

let empty_behavior = { algorithms = [] ; initial_algorithms = [] ; equations = [] ; initial_equations = [] ; external_ = None }

let empty_elements = { defs = [] ; extensions = [] ; redeclared_defs = [] ;
                       typedefs = [] ; redeclared_types = [] }
                        
                       
let empty_composition = { imports = [] ; public = empty_elements ; protected = empty_elements ; cargo = empty_behavior  }
                        
exception EmptyName

let rec name_ object_ = function
  | [] -> object_
  | field::r -> name_ (no_attr (Proj { object_ ; field })) r

let name = function
  | [] -> raise EmptyName
  | x::r -> name_ (no_attr (Ide x)) r
                         
let type_name xs = TName (List.map Location.mknoloc xs)

let root_type xs = TRootName (List.map Location.mknoloc xs)
                       
