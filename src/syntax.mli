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
 * Modelica 3.x abstract syntax
 *)
open Utils

type name = string list

                   
(**
 * The stored definition unit
 *)
type 'a commented = { commented : 'a ; comment : comment }
                      
and 'a annotated = { annotated_elem : 'a ; annotation : modification option; }

and comment = string option annotated
                     
and unit_ = { within : name option; toplevel_defs : typedef list }
                    
and typedef_options = { type_replaceable : bool ; type_final : bool ; partial : bool ; encapsulated : bool }
                         
and typedef_struct = { td_name : string ; sort : sort ; type_exp : texp ; cns : constraint_ option ; type_options : typedef_options }

and typedef = typedef_struct commented

and constraint_ = exp commented

and algorithm = statement list

and behavior = {algorithms : algorithm list ;
                equation : equation list ;
                initial_algorithm : algorithm list ;
                initial_equations : equation list ;
                external_ : external_def option }

and external_def_struct = { lang : string ; ext_lhs : exp option ; ext_ident : string ; ext_args : exp list }
and external_def = external_def_struct annotated
  

and class_spec = Composition of composition
               | Enumeration of enum_literal list
               | OpenEnumeration
               | DerSpec of der_spec
               | Extension of composition * (modification option)
                   
and composition = { typedefs : typedef list ;
                    redeclared_types : typedef list ;
                    imports : import list ; 
                    extensions : extend list ;
                    defs : definition list ;
                    redeclared_defs : definition list ;
                    cargo : behavior ;
                  }

and enum_literal = { enum_name : string ; c: comment }

and der_spec = { der_name : name ; idents : string list }

and sort = Package | Class | Model | Block | Connector | ExpandableConnector | Record
           | Function | Type | Operator | OperatorRecord | OperatorFunction 

and connectivity = Flow | Stream 

and variability = Constant | Parameter | Discrete 

and causality = Input | Output

and named_import = { from : name ; selected : string }

and import = import_desc commented
                     
and import_desc = NamedImport of named_import
                | Unnamed of name
                | UnqualifiedImport of name

and visibility = Public | Protected

and extend = { ext_type : texp ; ext_visibility : visibility ; ext_annotation : modification option }

and scope = Inner | Outer | InnerOuter | Local

and definition_options = { final : bool ; scope : scope ; visibility : visibility ; replaceable : bool }

and definition_structure = { def_name : string ; def_type : texp ; def_constraint : constraint_ option ;
                             def_rhs : exp option ; def_if : exp option ; def_options : definition_options }

and definition = definition_structure commented 

and statement = statement_desc commented 

and statements = statement list

and statement_desc = Assignment of assignment
                   | Call of call_statement
                   | IfStmt of if_statement
                   | WhenStmt of when_statement
                   | Break
                   | Return
                   | ForStmt of for_statement
                   | WhileStmt of while_statement

and assignment = { target : exp ; source : exp }

and call_statement = { procedure : exp ; pargs : exp list ; pnamed_args : exp StrMap.t}
                   
and 'a else_condition = { guard : exp ; elsethen : 'a }
                   
and 'a condition_struct = { condition : exp ; then_ : 'a ; else_if : 'a else_condition list ; else_ : 'a }
                   
and if_statement = statements condition_struct 

and when_statement = statements condition_struct

and 'a for_loop_struct = {idx : idx list ; body : 'a }
                                
and for_statement = statements for_loop_struct 

and while_statement = { while_ : exp ; do_ : statements }
  
and equations = equation list

and equation = equation_desc commented 

and equation_desc = SimpleEquation of simple_equation
                  | ForEquation of for_equation
                  | IfEquation of if_equation
                  | WhenEquation of when_equation
                  | ExpEquation of exp

and simple_equation = { eq_lhs : exp ; eq_rhs : exp }
                        
and for_equation = equations for_loop_struct

and if_equation = equations condition_struct

and when_equation = equations condition_struct

and binary_exp = { left : exp ; right : exp ; }

and if_expression = exp condition_struct 

and array_access =  { lhs : exp ; indices : exp list }

and range = { start : exp ; end_ : exp ; step : exp option }

and projection = { object_ : exp ; field : string }

and application = { fun_ : exp ; args : exp list ; named_args : exp StrMap.t }

and comprehension = { exp : exp ; idxs : idx list }
                    
and exp = Pow of binary_exp
        | DPow of binary_exp
        | Mul of binary_exp
        | DMul of binary_exp
        | Div of binary_exp
        | DDiv of binary_exp
        | Plus of binary_exp
        | DPlus of binary_exp
        | Minus of binary_exp
        | DMinus of binary_exp
        | UMinus of exp
        | UPlus of exp
        | UDMinus of exp
        | UDPlus of exp

        | And of binary_exp
        | Or of binary_exp
        | Not of exp

        | Gt of binary_exp
        | Lt of binary_exp
        | Leq of binary_exp
        | Geq of binary_exp
        | Neq of binary_exp
        | Eq of binary_exp

        | If of if_expression
        | ArrayAccess of array_access
        | Range of range
        | RootIde of string (* .foo *)
        | Ide of string 
        | Proj of projection
        | App of application
        | Bool of bool
        | Int of int
        | Real of float
        | String of string
        | Compr of comprehension
        | Array of exp list
        | MArray of (exp list) list
        | ExplicitClosure of exp
        | End | Colon | Empty | Der | Initial
        | Tuple of exp list
                       
and idx = { variable : string ; range : exp option }

and tprojection = { class_type : texp ; type_element : string }

and array_type = { base_type : texp ; dims : exp list }

and mod_type = { mod_type : texp ; modification : modification }
                   
and texp = TIde of string
         | TRootide of string
         | TProj of tprojection
         | TArray of array_type
         | TMod of mod_type
         | TVar of variability flagged_type
         | TCon of connectivity flagged_type
         | TCau of causality flagged_type
                             
and 'a flagged_type = { flag : 'a ; flagged : texp }
                     
and type_redeclaration = { redecl_each : bool ; redecl_type : typedef; }

and component_redeclaration = { each : bool ; def : definition; }

and component_modification_struct = { mod_each : bool ; mod_final : bool; mod_name : name; mod_modification : modification option ; mod_rhs : exp option }
                               
and component_modification = component_modification_struct commented
and modification = { types : type_redeclaration list ;
                     components : component_redeclaration list ;
                     modifications : component_modification list ; }

