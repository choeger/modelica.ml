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

(** Modelica 3.x abstract syntax 

    This module contains an interpretation of a "usable" form of the abstract syntax 
    of the modeling language {{: http://modelica.org}  Modelica}
    Since Modelica only specifies the {i concrete} syntax in the specification, there
    is a certain degree of freedom applied here.
    @author Christoph Höger

 *)
open Utils
open Location

type str = string loc [@@deriving yojson]
       
(** A type-name is a list of strings separated by dots, e.g. Modelica.Icons.Example *)
type name = str list [@@deriving yojson]
                    
 (** Something that can be commented can wrapped in this record *)
type 'a commented = { commented : 'a ; comment : comment }
                      
 (** Something that can be annotated can wrapped in this record *)
and 'a annotated = { annotated_elem : 'a ; annotation : modification option; }
                     
(** Comments are optionally annotated optional strings *)
and comment = str option annotated
                     
(** The stored definition unit is the representation of a single Modelica file *)
and unit_ = { within : name option; toplevel_defs : typedef list }
              
(** The options of a type-definition:
    is the definition replaceable / final / partial / encapsulated ? *)
and typedef_options = { type_replaceable : bool ; 
                        type_final : bool ; 
                        partial : bool ; 
                        encapsulated : bool }

(** Typedefs share a lot of common code. 
    This is reflected by the {! Syntax.typedef_struct }: {v 'a v} denotes the definition's distincitve payload. *)
and 'a typedef_struct = { td_name : str ; sort : sort ; type_exp : 'a ; cns : constraint_ option ; type_options : typedef_options }
                          
(** The definition of a new type/class etc. *)
and typedef_desc = Short of texp typedef_struct
                 | Composition of composition typedef_struct
                 | Enumeration of (enum_literal list) typedef_struct
                 | OpenEnumeration of unit typedef_struct
                 | DerSpec of der_spec typedef_struct
                 | Extension of extension typedef_struct

and extension = composition * modification option
                                                                      
and typedef = typedef_desc commented

and constraint_ = texp commented

and algorithm = statement list

and behavior = {algorithms : algorithm list ;
                equations : equation list ;
                initial_algorithms : algorithm list ;
                initial_equations : equation list ;
                external_ : external_def option }

and external_def_struct = { lang : string ; ext_lhs : exp option ; ext_ident : string ; ext_args : exp list }
and external_def = external_def_struct annotated

and elements = {
  typedefs : typedef list ;
  redeclared_types : typedef list ;
  extensions : extend list ;
  defs : definition list ;
  redeclared_defs : definition list ;
}
                   
and composition = { imports : import list ;
                    public : elements ;
                    protected : elements;
                    cargo : behavior ;
                  }

and enum_literal = string commented

(** Partial derivative specification, see section 12.7.2 *)
and der_spec = { der_name : name ; idents : str list }

and sort = Package | Class | Model | Block | Connector | ExpandableConnector | Record
           | Function | Type | Operator | OperatorRecord | OperatorFunction 

and connectivity = Flow | Stream 

and variability = Constant | Parameter | Discrete 

and causality = Input | Output

and named_import = { global : name ; local : str }

and import = import_desc commented
                     
and import_desc = NamedImport of named_import
                | Unnamed of name
                | UnqualifiedImport of name

and extend = { ext_type : texp ; ext_annotation : modification option }

and scope = Inner | Outer | InnerOuter | Local

and definition_options = { final : bool ; scope : scope ; replaceable : bool }

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

and named_arg = { argument_name : str ; argument : exp }
                   
and call_statement = { procedure : exp ; pargs : exp list ; pnamed_args : named_arg list }
                   
and 'a else_condition = { guard : exp ; elsethen : 'a }
                   
and 'a condition_struct = { condition : exp ; then_ : 'a ; else_if : 'a else_condition list ; else_ : 'a }
                   
and if_statement = statements condition_struct 

and when_statement = statements condition_struct

and 'a for_loop_struct = {idx : idx list ; body : 'a }
                                
and for_statement = statements for_loop_struct 

and while_statement = { while_ : exp ; do_ : statements }
  
and equations = equation list

and equation = equation_desc commented 

and equation_desc = SimpleEquation of binary_exp
                  | ForEquation of for_equation
                  | IfEquation of if_equation
                  | WhenEquation of when_equation
                  | ExpEquation of exp

and for_equation = equations for_loop_struct

and if_equation = equations condition_struct

and when_equation = equations condition_struct

and binary_exp = { left : exp ; right : exp ; }

and if_expression = exp condition_struct 

and array_access =  { lhs : exp ; indices : exp list }

and range = { start : exp ; end_ : exp ; step : exp option }

and projection = { object_ : exp ; field : string }

and application = { fun_ : exp ; args : exp list ; named_args : named_arg list }

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
        | End | Colon | Der | Initial | Assert
        | OutputExpression of exp option list
                                          
and idx = { variable : str ; range : exp option }

and tprojection = { class_type : texp ; type_element : string }

and array_type = { base_type : texp ; dims : exp list }

and mod_type = { mod_type : texp ; modification : modification }
                   
and texp = TName of name
         | TRootName of name
         | TArray of array_type
         | TMod of mod_type
         | TVar of variability flagged_type
         | TCon of connectivity flagged_type
         | TCau of causality flagged_type
                             
and 'a flagged_type = { flag : 'a ; flagged : texp }
                     
and type_redeclaration = { redecl_each : bool ; redecl_type : texp typedef_struct commented ; }

and component_redeclaration = { each : bool ; def : definition; }

and component_modification_struct = { mod_each : bool ; mod_final : bool; mod_name : name;
                                      mod_value : modification_value option ; }

and modification_value = Nested of modification
                       | Rebind of exp
                       | NestedRebind of nested_and_rebind_modification

and nested_and_rebind_modification = { nested : modification ; new_value : exp }
                               
and component_modification = component_modification_struct commented

and modification = { types : type_redeclaration list ;
                     components : component_redeclaration list ;
                     modifications : component_modification list ; }

