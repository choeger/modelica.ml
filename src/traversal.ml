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

open Batteries
open Syntax

open Mapper
open Folder

type ('s, 'a) fold_method = ('a folder) -> 's -> 'a -> 'a
       
module type TRAVERSAL = sig
    type sort

    val fold : (sort, 'a) Folder.fold_method
    val map : sort Mapper.map_method
  end

module DerSpec = struct
  type sort = der_spec

  let fold this { der_name ; idents } a = let a' = this.fold_name this der_name a in
                                          fold_list (fold_located this.fold_identifier) this idents a'

  let map this { der_name ; idents } =
    { der_name = this.name this der_name ;
      idents = map_list (map_located this.identifier) this idents } 
end
                    
module Unit = struct
  type sort = unit_
  
  let fold this { within; toplevel_defs; } a = let a' = this.fold_within this within a in
                                               fold_list this.fold_typedef this toplevel_defs a'
                                               
  let map this { within; toplevel_defs; } = { within = this.within this within ;
                                              toplevel_defs = map_list this.typedef this toplevel_defs }
end

module TD = struct
  type sort = typedef
  
  let map_tds sub this { td_name ; sort ; type_exp ; cns ; type_options } =
    let type_options = this.typedef_options this type_options in
    let type_exp = sub this type_exp in
    let cns = Option.map (this.constraint_ this) cns in
    { td_name ; sort ; type_exp ; cns ; type_options }

  let map_desc this = function
      Short tds -> Short (map_tds this.texp this tds)
    | Composition tds -> Composition (map_tds this.composition this tds)
    | Extension tds -> Extension (map_tds this.extension this tds)
    | Enumeration tds -> Enumeration (map_tds (map_list this.enum_literal) this tds)
    | OpenEnumeration tds -> OpenEnumeration (map_tds id this tds)       
    | DerSpec tds -> DerSpec (map_tds this.der_spec this tds)
                                                         
  let map = map_commented map_desc

  let fold_tds sub this { td_name ; sort ; type_exp ; cns ; type_options } =
    (sub this type_exp) %>
      (fold_option this.fold_constraint_ this cns) %>
      (this.fold_typedef_options this type_options)
                          
  let fold_desc this = function
      Short tds -> fold_tds this.fold_texp this tds
    | Composition tds -> fold_tds this.fold_composition this tds
    | Extension tds -> fold_tds this.fold_extension this tds
    | Enumeration tds -> fold_tds (fold_list this.fold_enum_literal) this tds
    | OpenEnumeration tds -> fold_tds fold_id this tds
    | DerSpec tds -> fold_tds this.fold_der_spec this tds
                          
  let fold = fold_commented fold_desc
                          
end

module Import = struct 
  type sort = import
  
  let map this = map_commented this.import_desc this

  let fold this = fold_commented this.fold_import_desc this
end

module Comment = struct
  type sort = comment
  
  let fold this { annotated_elem ; annotation } =
    fold_option (fold_located this.fold_comment_str) this annotated_elem %>
      fold_option this.fold_annotation this annotation 
  
  let map this { annotated_elem ; annotation } = { annotated_elem = (map_option &&& map_located) this.comment_str this annotated_elem ;
                                                   annotation = map_option this.annotation this annotation }
end

module Name = struct
  type sort = name

  let fold this = fold_list (fold_located this.fold_identifier) this
                
  let map this = map_list (map_located this.identifier) this
end

module TRD = struct
  type sort = type_redeclaration

  let fold this { redecl_each ; redecl_type } = fold_commented (TD.fold_tds this.fold_texp) this redecl_type
                
  let map this { redecl_each ; redecl_type } =
    { redecl_each ; redecl_type = map_commented (TD.map_tds this.texp) this redecl_type }
end

module CRD = struct
  type sort = component_redeclaration 

  let fold this { each ; def } = this.fold_def this def
                
  let map this { each ; def } =
    { each ; def = this.def this def }
end

module CMOD = struct
  type sort = component_modification
  
  let fold this = fold_commented this.fold_component_modification_struct this 
  
  let map this = (map_commented this.component_modification_struct) this
end
               
module CMOD_Struct = struct
  type sort = component_modification_struct

  let fold this { mod_each ; mod_final ; mod_name ;
                  mod_value ; } =
    this.fold_name this mod_name %>
      fold_option this.fold_modification_value this mod_value 

  let map this { mod_each ; mod_final ; mod_name ;
                 mod_value ; } = {mod_each ; mod_final ;
                                  mod_name = this.name this mod_name ;                                  
                                  mod_value = map_option this.modification_value this mod_value }
end

module CMOD_Value = struct
  type sort = modification_value

  let fold this = function
      Nested modification -> this.fold_modification this modification
    | Rebind exp -> this.fold_exp this exp
    | NestedRebind { nested ; new_value } -> this.fold_modification this nested %> this.fold_exp this new_value
                
  let map this = function
      Nested modification -> Nested (this.modification this modification)
    | Rebind exp -> Rebind (this.exp this exp)
    | NestedRebind { nested ; new_value } -> NestedRebind { nested = this.modification this nested ;
                                                            new_value = this.exp this new_value
                                                          }
end
                       
module Modification = struct
  type sort = modification

  let fold this {types ; components; modifications } =
    fold_list this.fold_type_redeclaration this types %>
      fold_list this.fold_component_redeclaration this components %>
        fold_list this.fold_component_modification this modifications
                
  let map this {types ; components; modifications } = { types = map_list this.type_redeclaration this types ;
                                                        components = map_list this.component_redeclaration this components ;
                                                        modifications = map_list this.component_modification this modifications }
end

module Equation_Desc = struct
  type sort = equation_desc
                
  let fold this = function
    | SimpleEquation {left; right} -> this.fold_exp this left %> this.fold_exp this right
    | ForEquation loop -> fold_for_loop (fold_list this.fold_equation) this loop
    | IfEquation ifeq -> fold_conditional (fold_list this.fold_equation) this ifeq
    | WhenEquation when_eq -> fold_conditional (fold_list this.fold_equation) this when_eq
    | ExpEquation exp -> this.fold_exp this exp
      
  let map this = function
    | SimpleEquation { left ; right } -> SimpleEquation { left = this.exp this left ;
                                                          right = this.exp this right }
    | ForEquation loop -> ForEquation (map_for_loop (map_list this.equation) this loop)
    | IfEquation ifeq -> IfEquation (map_conditional (map_list this.equation) this ifeq)
    | WhenEquation when_eq -> WhenEquation (map_conditional (map_list this.equation) this when_eq)
    | ExpEquation exp -> ExpEquation (this.exp this exp)
end

module Equation = struct
  type sort = equation
  let fold this = fold_commented this.fold_equation_desc this
  let map this = map_commented this.equation_desc this
end

module Idx = struct
  type sort = idx

  let fold this { variable ; range } = fold_located this.fold_identifier this variable %>
                                         fold_option this.fold_exp this range
                
  let map this { variable ; range } = { variable = map_located this.identifier this variable ;
                                        range = map_option this.exp this range  }
end

module Algorithm = struct
  type sort = statement list

  let fold this = fold_list this.fold_statement this
  
  let map this = map_list this.statement this 
end

module Statement = struct
  type sort = statement

  let fold this = fold_commented this.fold_statement_desc this
                
  let map this = map_commented this.statement_desc this
end

module Statement_Desc = struct
  type sort = statement_desc

  let fold this = function
      Assignment { target ; source } ->  this.fold_exp this target %>
                                           this.fold_exp this source

    | Call {procedure; pargs; pnamed_args} -> this.fold_exp this procedure %>
                                                fold_list this.fold_exp this pargs %>
                                                  fold_list this.fold_named_arg this pnamed_args
                                                   
    | IfStmt if_statement -> fold_conditional (fold_list this.fold_statement) this if_statement                                              
    | WhenStmt when_statement -> fold_conditional (fold_list this.fold_statement) this when_statement
    | Break -> fun a -> a
    | Return -> fun a -> a
    | ForStmt for_statement -> fold_for_loop (fold_list this.fold_statement) this for_statement
                                             
    | WhileStmt { while_ ; do_ } -> this.fold_exp this while_ %>
                                      fold_list this.fold_statement this do_ 
  
  let map this = function
      Assignment { target ; source } -> Assignment { target = this.exp this target ;
                                                     source = this.exp this source }

    | Call {procedure; pargs; pnamed_args} -> Call { procedure = this.exp this procedure ;
                                                     pargs = map_list this.exp this pargs ;
                                                     pnamed_args = map_list this.named_arg this pnamed_args }
                                                   
    | IfStmt if_statement -> IfStmt (map_conditional (map_list this.statement) this if_statement) 
    | WhenStmt when_statement -> WhenStmt (map_conditional (map_list this.statement) this when_statement) 
    | Break -> Break
    | Return -> Return
    | ForStmt for_statement -> ForStmt (map_for_loop (map_list this.statement) this for_statement)
    | WhileStmt { while_ ; do_ } -> WhileStmt { while_ = this.exp this while_ ;
                                                do_ = map_list this.statement this do_ }
end

module Named_Arg = struct
  type sort = named_arg

  let fold this {argument_name ; argument} = fold_located this.fold_identifier this argument_name %>
                                               this.fold_exp this argument
                
  let map this { argument_name ; argument } = { argument_name = map_located this.identifier this argument_name ;
                                                argument = this.exp this argument }
end

module Exp = struct
  type sort = exp

  let map_binary this {left ; right } = {left=this.exp this left ; right = this.exp this right }
  let fold_binary this {left; right } = this.fold_exp this left %> this.fold_exp this right

  let fold this = function
    | Pow b -> fold_binary this b
    | DPow b -> fold_binary this b
    | Mul b -> fold_binary this b
    | DMul b -> fold_binary this b
    | Plus b -> fold_binary this b
    | DPlus b -> fold_binary this b
    | Div b -> fold_binary this b
    | DDiv b -> fold_binary this b
    | Minus b -> fold_binary this b
    | DMinus b -> fold_binary this b
    | And b -> fold_binary this b
    | Or b -> fold_binary this b
    | Gt b -> fold_binary this b
    | Lt b -> fold_binary this b
    | Leq b -> fold_binary this b
    | Geq b -> fold_binary this b
    | Neq b -> fold_binary this b
    | Eq b -> fold_binary this b

    | UMinus e -> this.fold_exp this e
    | UPlus e -> this.fold_exp this e
    | UDPlus e -> this.fold_exp this e
    | UDMinus e -> this.fold_exp this e
    | Not e -> this.fold_exp this e

    | If if_expression -> fold_conditional this.fold_exp this if_expression
    | ArrayAccess {lhs; indices} -> this.fold_exp this lhs %> fold_list this.fold_exp this indices

    | Range {start; end_; step} -> this.fold_exp this start %>
                                     this.fold_exp this end_ %>
                                       fold_option this.fold_exp this step

    | Ide s -> this.fold_identifier this s
    | Proj {object_; field} -> this.fold_exp this object_ 
    | App { fun_; args; named_args} -> this.fold_exp this fun_ %>
                                         fold_list this.fold_exp this args %>
                                           fold_list this.fold_named_arg this named_args

    | Compr { exp ; idxs } -> this.fold_exp this exp %>
                                fold_list this.fold_idx this idxs
                                
    | Array es -> fold_list this.fold_exp this es
    | MArray ess -> fold_list (fold_list this.fold_exp) this ess
    | ExplicitClosure e -> this.fold_exp this e                           
    | OutputExpression eos -> fold_list (fold_option this.fold_exp) this eos
    | ( End | Colon | Der | Initial | Assert | Bool _ | Int _ | Real _ | String _ | RootIde _) -> fun a -> a
                             
  let map this = function
    | Pow b -> Pow (map_binary this b)
    | DPow b -> DPow (map_binary this b)
    | Mul b -> Mul (map_binary this b)
    | DMul b -> DMul (map_binary this b)
    | Div b -> Div (map_binary this b)
    | DDiv b -> DDiv (map_binary this b)
    | Plus b -> Plus (map_binary this b)
    | DPlus b -> DPlus (map_binary this b)
    | Minus b -> Minus (map_binary this b)
    | DMinus b -> DMinus (map_binary this b)

    | UMinus e -> UMinus (this.exp this e)
    | UPlus e -> UPlus (this.exp this e)
    | UDPlus e -> UDPlus (this.exp this e)
    | UDMinus e -> UDMinus (this.exp this e)

    | Not e -> Not (this.exp this e)
    | And b -> And (map_binary this b)
    | Or b -> Or (map_binary this b)
    | Gt b -> Gt (map_binary this b)
    | Lt b -> Lt (map_binary this b)
    | Leq b -> Leq (map_binary this b)
    | Geq b -> Geq (map_binary this b)
    | Neq b -> Neq (map_binary this b)
    | Eq b -> Eq (map_binary this b)

    | If if_expression -> If (map_conditional this.exp this if_expression)
    | ArrayAccess {lhs; indices} -> ArrayAccess { lhs = this.exp this lhs ; indices = map_list this.exp this indices }

    | Range {start; end_; step} -> Range { start = this.exp this start ;
                                           end_ = this.exp this end_ ;
                                           step = map_option this.exp this step }

    | RootIde s -> RootIde s
    | Ide s -> Ide s
    | Proj {object_; field} -> Proj { object_ = this.exp this object_ ; field }
    | App { fun_; args; named_args} -> App { fun_ = this.exp this fun_ ;
                                             args = map_list this.exp this args ;
                                             named_args = map_list this.named_arg this named_args }

    | Compr { exp ; idxs } -> Compr { exp = this.exp this exp;
                                      idxs = map_list this.idx this idxs }
                                
    | Array es -> Array (map_list this.exp this es)
    | MArray ess -> MArray (map_list (map_list this.exp) this ess)
    | ExplicitClosure e -> ExplicitClosure (this.exp this e)                           
    | OutputExpression eos -> OutputExpression (map_list (map_option this.exp) this eos)
    | ( End | Colon | Der | Initial | Assert | Bool _ | Int _ | Real _ | String _) as e -> e


end
                              
let default_folder = {
  fold_unit_ = Unit.fold ;
  fold_within = fold_id;
  fold_comment = fold_id;
  fold_annotation = fold_id;
  fold_typedef_options = fold_id;
  fold_typedef = TD.fold;
  fold_composition = fold_id;
  fold_redeclared_typedef = TD.fold;
  fold_extension = fold_id;
  fold_def = fold_id;
  fold_redeclared_def = fold_id;
  fold_import = fold_id;
  fold_import_desc = fold_id;
  fold_imports = fold_id;
  fold_public = fold_id;
  fold_protected = fold_id;
  fold_cargo = fold_id;
  fold_constraint_ = fold_id;
  fold_der_spec = fold_id;
  fold_enum_literal = fold_id;
  fold_algorithm = fold_id;
  fold_external_def = fold_id;
  fold_texp = fold_id;
  fold_exp = fold_id;
  fold_idx = fold_id;
  fold_statement_desc = fold_id;
  fold_statement = fold_id;
  fold_equation_desc = fold_id;
  fold_equation = fold_id;
  fold_modification = fold_id;
  fold_type_redeclaration = fold_id;
  fold_component_redeclaration = fold_id;
  fold_component_modification = fold_id;
  fold_component_modification_struct = fold_id;
  fold_modification_value = fold_id;
  fold_name = fold_id;
  fold_named_arg = fold_id;
  fold_identifier = fold_id;
  fold_comment_str = fold_id;
  fold_location = fold_id;
}
