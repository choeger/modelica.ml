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

open Syntax
open Utils

type class_ = Hierarchy of hierarchy
            | Reference of name
            | RootReference of name
            | Primitive of string * (class_ list)
            | Method of string list

 and hierarchy = { fields : class_field list ; super : class_ list }
                               
 and class_element = { element_name : string ; element_rhs : class_ }
                       
 and class_field = Named_element of class_element
                 | Replaceable of class_element
                 | Function of class_element

type t = class_

type ptr = { named : string list ; super_class : int option } 
       
let rec translate_tds = function
  | Short tds -> Named_element { element_name = tds.td_name ; element_rhs = translate_texp tds.type_exp }
                               
  | Composition tds -> begin
      match tds.sort with
        Function | OperatorFunction -> Function { element_name = tds.td_name ; element_rhs = translate_comp tds.type_exp }
        | _ -> Named_element { element_name = tds.td_name ; element_rhs = translate_comp tds.type_exp }
    end
                            
  | Enumeration tds -> Named_element { element_name = tds.td_name ; element_rhs =  Primitive ("enumeration", []) }
  | OpenEnumeration tds ->Named_element { element_name = tds.td_name ; element_rhs =   Primitive ("open enumeration", []) }
  | DerSpec tds -> Named_element { element_name = tds.td_name ; element_rhs =  Primitive ("der", [Reference tds.type_exp.der_name]) }
  | Extension tds -> Named_element { element_name = tds.td_name ; element_rhs =  Primitive ("extension",[]) }

and translate_topdefs tds = Hierarchy {fields = List.map translate_typedef tds; super=[]}
                                   
and translate_typedef td = translate_tds td.commented
                                   
and translate_extends {ext_type} = translate_texp ext_type
                                   
and translate_elements {extensions;typedefs;redeclared_types} = 
  let super = List.map translate_extends extensions in
  let own_fields = List.map translate_typedef typedefs in
  let overloaded = List.map translate_typedef redeclared_types in
  {fields = overloaded @ own_fields ; super }
  
and translate_comp { public ; protected; } =
  let public = translate_elements public in
  let protected = translate_elements protected in
  Hierarchy {fields = public.fields @ protected.fields ; super = public.super @ protected.super }

and translate_redeclarations {types} =
  List.map (fun trd -> translate_tds (Short trd.redecl_type.commented)) types
    
and translate_texp = function
  | TName n -> Reference n
  | TRootName n -> RootReference n
                                 
  | TArray {base_type} -> Primitive("Array", [translate_texp base_type])
  | TMod {mod_type; modification} -> Hierarchy {super=[translate_texp mod_type]; fields = translate_redeclarations modification}
  | TVar {flagged} -> Primitive ("Variability", [translate_texp flagged] )
  | TCon {flagged} -> Primitive ("Connectivity", [translate_texp flagged] )
  | TCau {flagged} -> Primitive ("Causality", [translate_texp flagged] )

                                  
