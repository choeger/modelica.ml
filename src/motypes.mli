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
(*
open Syntax
open Utils
       
type type_ = Int | Real | String | Bool
             | Array of array_struct
             | ExternalObject of type_ object_struct
             | Enumeration of StrSet.t
             | Record of type_ object_struct
             | Package of type_ object_struct
             | Model of component_type object_struct
             | Recursive of recursive_struct
             | Function of function_type
             | Variable of string

 and recursive_struct = { recursive_name : string ; recursive_rhs : type_ }

 and array_struct = { element : type_ ; dimensions : int }

 and 'a object_struct = { dynamic_fields : 'a StrMap.t ; static_fields : type_ StrMap.t ; typedefs : 'a StrMap.t }                         
                             
 and function_type = { inputs : (string * type_) StrMap.t ; outputs : type_ list }
                                              
 and component_type = { cmp_variability : variability ;
                        cmp_causality : causality ;
                        cmp_connectivity : connectivity ;
                        cmp_type : type_ }


type typed_if_expression = typed_exp condition_struct 

 and typed_binary_exp = { left : typed_exp ; right : typed_exp ; }

 and typed_array_access =  { lhs : typed_exp ; indices : typed_exp list }

 and typed_range = { start : typed_exp ; end_ : exp ; step : typed_exp option }

 and typed_projection = { objectyped_ : typed_exp ; field : string }

 and typed_application = { fun_ : typed_exp ; args : typed_exp list ; named_args : named_arg list }

 and typed_comprehension = { exp : typed_exp ; idxs : idx list }

 and typed_exp = { structure : typed_exp structure ; type_ : type_ }
                             
 and typed_exp_structure = T_Pow of typed_binary_exp
                         | T_DPow of typed_binary_exp
                         | T_Mul of typed_binary_exp
                         | T_DMul of typed_binary_exp
                         | T_Div of typed_binary_exp
                         | T_DDiv of typed_binary_exp
                         | T_Plus of typed_binary_exp
                         | T_DPlus of typed_binary_exp
                         | T_Minus of typed_binary_exp
                         | T_DMinus of typed_binary_exp
                         | T_UMinus of typed_exp
                         | T_UPlus of typed_exp
                         | T_UDMinus of typed_exp
                         | T_UDPlus of typed_exp

                         | T_And of typed_binary_exp
                         | T_Or of typed_binary_exp
                         | T_Not of typed_exp

                         | T_Gt of typed_binary_exp
                         | T_Lt of typed_binary_exp
                         | T_Leq of typed_binary_exp
                         | T_Geq of typed_binary_exp
                         | T_Neq of typed_binary_exp
                         | T_Eq of typed_binary_exp

                         | T_If of typed_if_expression
                         | T_ArrayAccess of typed_array_access
                         | T_Range of typed_range
                         | T_RootIde of typed_str (* .foo *)
                         | T_Ide of typed_str 
                         | T_Proj of typed_projection
                         | T_App of typed_application
                         | T_Bool of bool
                         | T_Int of int
                         | T_Real of float
                         | T_String of string
                         | T_Compr of typed_comprehension
                         | T_Array of typed_exp list
                         | T_MArray of (typed_exp list) list
                         | T_ExplicitClosure of typed_exp
                         | T_End | T_Colon | T_Der | T_Initial | T_Assert
                         | T_OutputExpression of typed_exp option list
 *)
