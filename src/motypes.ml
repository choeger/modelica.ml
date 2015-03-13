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
open Utils
open Ast.Flags

module DS = Syntax

type ('f,'e) flagged_struct = { flag : 'f; flagged : 'e } [@@deriving show,yojson]
                                                                                                                                                                                    
type class_term = Reference of DS.name
                | RootReference of DS.name
                | PReplaceable of class_term
                | Redeclaration of redeclaration
                | StrictRedeclaration of redeclaration
                | PInt | PReal | PString | PBool | PExternalObject
                | PArray of constr_array
                | PClass of constr_class
                | PEnumeration of StrSet.t
                | PDer of DS.der_spec
                | PSort of sort_defined_struct
                | PVar of (variability, class_term) flagged_struct
                | PCau of (causality, class_term) flagged_struct
                | PCon of (connectivity, class_term) flagged_struct
                                                     [@@deriving yojson,show]

 and redeclaration = { rd_lhs : class_term ; rds : redeclared_element list }

 and redeclared_element = ClassMember of redecl_struct | Field of redecl_struct
                       
 and redecl_struct = { rd_name : string ; rd_rhs : class_term }
                       
 and sort_defined_struct = { defined_sort : sort ; rhs : class_term }
                                                     
 and constr_class = { class_sort : sort ; public : hierarchy ; protected : hierarchy }
                                                       
 and constr_array = { array_arg : class_term ; dimensions : int } 
                                              
 and hierarchy = { class_members : class_term StrMap.t ; super : class_term list ; fields : class_term StrMap.t }                               

module Normalized = struct

    type variability = Constant | Discrete | Parameter | Continuous [@@deriving show,yojson]
    type causality = Input | Output | Acausal [@@deriving show,yojson]
    type connectivity = Flow | Stream | Potential [@@deriving show,yojson]                                                     

    let cau_from_ast =
      function Ast.Flags.Input -> Input
             | Ast.Flags.Output -> Output
    let var_from_ast =
      function Ast.Flags.Constant -> Constant
             | Ast.Flags.Parameter -> Parameter
             | Ast.Flags.Discrete -> Discrete
    let con_from_ast =
      function Ast.Flags.Flow -> Flow
             | Ast.Flags.Stream -> Stream
    
    type class_value = Int | Real | String | Bool | Unit | ProtoExternalObject
                       | Array of array_struct
                       | ExternalObject of class_value StrMap.t
                       | Enumeration of StrSet.t
                       | Function of function_struct
                       | Class of object_struct
                       | Replaceable of replaceable_value
                       | Delayed of delayed_value
                                      [@@deriving show,yojson]

     and replaceable_value = { current : class_value ; replaceable_body : class_term ; replaceable_env : Class_deps.scope }
                                           
     and delayed_value = { environment : Class_deps.scope ; expression : class_term ; def_label : DS.name }
                                  
     and array_struct = { element : class_value ; dimensions : int } 

     and object_struct = { object_sort : sort ; public : elements_struct ; protected : elements_struct }
                                                                 
     and elements_struct = { class_members : type_annotation StrMap.t ; super : class_value list ;
                             dynamic_fields : type_annotation StrMap.t ; static_fields : class_value StrMap.t }
                             
     and function_struct = { inputs : (string * class_value) StrMap.t ; outputs : class_value list }

     and level2_type = { l2_variability : variability ;
                         l2_causality : causality ;
                         l2_connectivity : connectivity ;
                         l2_type : class_value }
                        
     and type_annotation = SimpleType of class_value | Level2Type of level2_type | UnknownType

    let default_level2 l2_type = {l2_variability=Constant; l2_causality=Acausal; l2_connectivity=Potential; l2_type}
                                                                                     
    let empty_elements = {class_members = StrMap.empty ; super = []; dynamic_fields=StrMap.empty ;static_fields=StrMap.empty}

    let empty_class_body = {public=empty_elements;protected=empty_elements;object_sort=Class}
                           
    let empty_class = Class empty_class_body

    let empty_class_ta = SimpleType empty_class
  end
                                                                                           
                               

                                                                                   

