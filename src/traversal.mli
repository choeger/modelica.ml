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

module type TRAVERSAL = sig
    type sort

    val fold : (sort, 'a) Folder.fold_method
    val map : sort Mapper.map_method
  end

                          
module Unit : TRAVERSAL with type sort = unit_

module DerSpec : TRAVERSAL with type sort = der_spec
(*
module Name = struct
  let map this = map_list (map_located this.identifier) this
end

module Import_Desc = struct
  let map this = function
      NamedImport { global ; local } -> NamedImport { global = this.name this global ; local }
    | Unnamed name -> Unnamed (this.name this name)
    | UnqualifiedImport name -> UnqualifiedImport (this.name this name)

end
                
module Import = struct
  let map this = map_commented this.import_desc this
end

module Comment = struct
  let map this { annotated_elem ; annotation } = { annotated_elem = (map_option &&& map_located) this.comment_str this annotated_elem ;
                                                   annotation = map_option this.annotation this annotation }
end

module TRD = struct
  (** Map type redeclarations *)
  let map this { redecl_each ; redecl_type } =
    { redecl_each ; redecl_type = map_commented (TD.map_tds this.texp) this redecl_type }
end

module CRD = struct
  (** Map component redeclarations *)
  let map this { each ; def } =
    { each ; def = this.def this def }
end

module CMOD = struct
  let map this = (map_commented this.component_modification_struct) this
end
               
module CMOD_Struct = struct
  (** Map component modifications *)
  let map this { mod_each ; mod_final ; mod_name ;
                 mod_value ; } = {mod_each ; mod_final ;
                                  mod_name = this.name this mod_name ;                                  
                                  mod_value = map_option this.modification_value this mod_value }
end

module CMOD_Value = struct
  let map this = function
      Nested modification -> Nested (this.modification this modification)
    | Rebind exp -> Rebind (this.exp this exp)
    | NestedRebind { nested ; new_value } -> NestedRebind { nested = this.modification this nested ;
                                                            new_value = this.exp this new_value
                                                          }
end
                       
module Modification = struct
  let map this {types ; components; modifications } = { types = map_list this.type_redeclaration this types ;
                                                        components = map_list this.component_redeclaration this components ;
                                                        modifications = map_list this.component_modification this modifications }
end

module Equation_Desc = struct
  let map this = function
    | SimpleEquation { left ; right } -> SimpleEquation { left = this.exp this left ;
                                                          right = this.exp this right }
    | ForEquation loop -> ForEquation (map_for_loop (map_list this.equation) this loop)
    | IfEquation ifeq -> IfEquation (map_conditional (map_list this.equation) this ifeq)
    | WhenEquation when_eq -> WhenEquation (map_conditional (map_list this.equation) this when_eq)
    | ExpEquation exp -> ExpEquation (this.exp this exp)
end

module Equation = struct
  let map this = map_commented this.equation_desc this
end
         
module Idx = struct
  let map this { variable ; range } = { variable = map_located id this variable ;
                                        range = map_option this.exp this range  }
end

module Algorithm = struct
  let map this = map_list this.statement this 
end

module Statement = struct
  let map this = map_commented this.statement_desc this
end

module Statement_Desc = struct
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
  let map this { argument_name ; argument } = { argument_name = map_located this.identifier this argument_name ;
                                                argument = this.exp this argument }
end


module Exp = struct
  let map_binary this {left ; right } = {left=this.exp this left ; right = this.exp this right }
                                          
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
 *)
