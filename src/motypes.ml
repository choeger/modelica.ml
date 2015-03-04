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
       
type type_ = Int | Real | String | Bool | Unit
             | Array of array_struct
             | ExternalObject of object_struct
             | Enumeration of StrSet.t
             | Record of object_struct
             | Package of object_struct
             | Function of function_type
                             [@@deriving show,yojson]
                             
 and recursive_struct = { recursive_name : string ; recursive_rhs : type_ } [@@deriving show,yojson]

 and array_struct = { element : type_ ; dimensions : int } [@@deriving show,yojson]

 and object_struct = { dynamic_fields : type_ StrMap.t ; static_fields : type_ StrMap.t } [@@deriving show,yojson]
                             
 and function_type = { inputs : (string * type_) StrMap.t ; outputs : type_ list } [@@deriving show,yojson]

type class_ = Hierarchy of hierarchy
            | Reference of DS.name
            | RootReference of DS.name
            | Primitive of type_construct
            | Method of string list
                               [@@deriving yojson,show]

 and type_construct = PInt | PReal | PString | PBool | PExternalObject
                      | PArray of constr_array
                      | PEnumeration of StrSet.t
                      | PVar of constr_var
                      | PConn of constr_conn
                      | PDer of DS.der_spec
                      | PCaus of constr_caus
                                   [@@deriving yojson]

 and constr_array = { array_arg : class_ ; dimensions : int }

 and constr_var = { var_arg : class_ ; constr_variability : variability }
 and constr_conn = { conn_arg : class_ ; conn_variability : variability }
 and constr_caus = { caus_arg : class_ ; caus_variability : variability }
                                              
 and hierarchy = { fields : class_element StrMap.t ; super : class_ list }
                               
 and class_element = { kind : class_element_kind ; body : class_ }

 and class_element_kind = Static
                        | Replaceable
                        | Function
                       
type level2_type = { l2_variability : variability ;
                     l2_causality : causality ;
                     l2_connectivity : connectivity ;
                     l2_type : type_ } [@@deriving show,yojson]
                        
 and type_annotation = SimpleType of type_ | Level2Type of level2_type | UnknownType [@@deriving show,yojson]
                                                                           
type class_value = VHierarchy of value_hierarchy
                 | VPrimitive of type_annotation
                 | VMethod of string list
                 | VDelayed of delayed_value
                                 [@@deriving show,yojson]

 and delayed_value = { environment : scope ; expression : class_ ; def_label : DS.name }
                                 
 and value_hierarchy = { vfields : class_value_element StrMap.t ; vsuper : class_value list }
                               
 and class_value_element = { vkind : class_element_kind ; vbody : class_value }

                                                                                   

