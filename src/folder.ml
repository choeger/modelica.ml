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

module type S = sig
    module Syntax : Generic_syntax.S
    open Syntax 
    type ('s, 'a) fold_method = ('a folder) -> 's -> 'a -> 'a
     and 'a folder = {
         fold_unit_ : (unit_,'a) fold_method;
         fold_within : (name option,'a) fold_method;
         fold_comment : (comment,'a) fold_method;
         fold_annotation : (modification,'a) fold_method;
         fold_typedef_options : (typedef_options,'a) fold_method;
         fold_typedef : (typedef,'a) fold_method;
         fold_typedef_desc : (typedef_desc,'a) fold_method;
         fold_composition : (composition,'a) fold_method;
         fold_redeclared_typedef : (typedef,'a) fold_method;
         fold_extension : (extension,'a) fold_method;
         fold_def : (definition,'a) fold_method;
         fold_definition_structure : (definition_structure, 'a) fold_method;
         fold_definition_options : (definition_options, 'a) fold_method;
         fold_redeclared_def : (definition,'a) fold_method;
         fold_import : (import,'a) fold_method;
         fold_import_desc : (import_desc,'a) fold_method;
         fold_imports : (import list,'a) fold_method;
         fold_public : (elements,'a) fold_method;
         fold_protected : (elements,'a) fold_method;
         fold_extends : (extend, 'a) fold_method; 
         fold_cargo : (behavior,'a) fold_method;
         fold_constraint : (constraint_,'a) fold_method;
         fold_der_spec : (der_spec,'a) fold_method;
         fold_enum_literal : (enum_literal,'a) fold_method;
         fold_algorithm : (algorithm,'a) fold_method;
         fold_external_def : (external_def,'a) fold_method;
         fold_texp : (texp,'a) fold_method;
         fold_exp : (exp,'a) fold_method;
         fold_exp_struct : (exp_struct,'a) fold_method;
         fold_attr : (attr,'a) fold_method;
         fold_idx : (idx,'a) fold_method;
         fold_statement_desc : (statement_desc,'a) fold_method;
         fold_statement : (statement,'a) fold_method;
         fold_equation_desc : (equation_desc,'a) fold_method;
         fold_equation : (equation,'a) fold_method;
         fold_modification : (modification,'a) fold_method;
         fold_type_redeclaration : (type_redeclaration,'a) fold_method;
         fold_component_redeclaration : (component_redeclaration,'a) fold_method;
         fold_component_modification : (component_modification,'a) fold_method;
         fold_component_modification_struct : (component_modification_struct,'a) fold_method;
         fold_modification_value : (modification_value,'a) fold_method;
         fold_name : (name,'a) fold_method;
         fold_named_arg : (named_arg,'a) fold_method;
         fold_identifier : (string,'a) fold_method;
         fold_comment_str : (string,'a) fold_method;
         fold_location : (Location.t,'a) fold_method;                              
       }  
    val fold_id : ('sort,'a) fold_method
    val fold_commented : ('sort, 'a) fold_method -> ('sort commented, 'a) fold_method
    val fold_located : ('sort, 'a) fold_method -> ('sort Location.loc, 'a) fold_method
    val fold_list : ('sort, 'a) fold_method -> ('sort list, 'a) fold_method
    val fold_option : ('sort, 'a) fold_method -> ('sort option, 'a) fold_method                                                           
    val fold_for_loop : ('sort, 'a) fold_method -> ('sort for_loop_struct, 'a) fold_method                                                           
    val fold_conditional : ('sort, 'a) fold_method -> ('sort condition_struct, 'a) fold_method                                                           
  end

module Make(Tree : Generic_syntax.S) = struct
    type attr = Tree.attr
    module Syntax = Tree
    open Syntax
           
    type ('s, 'a) fold_method = ('a folder) -> 's -> 'a -> 'a

     and 'a folder = {
         fold_unit_ : (unit_,'a) fold_method;
         fold_within : (name option,'a) fold_method;
         fold_comment : (comment,'a) fold_method;
         fold_annotation : (modification,'a) fold_method;
         fold_typedef_options : (typedef_options,'a) fold_method;
         fold_typedef : (typedef,'a) fold_method;
         fold_typedef_desc : (typedef_desc,'a) fold_method;
         fold_composition : (composition,'a) fold_method;
         fold_redeclared_typedef : (typedef,'a) fold_method;
         fold_extension : (extension,'a) fold_method;
         fold_def : (definition,'a) fold_method;
         fold_definition_structure : (definition_structure, 'a) fold_method;
         fold_definition_options : (definition_options, 'a) fold_method;
         fold_redeclared_def : (definition,'a) fold_method;
         fold_import : (import,'a) fold_method;
         fold_import_desc : (import_desc,'a) fold_method;
         fold_imports : (import list,'a) fold_method;
         fold_public : (elements,'a) fold_method;
         fold_protected : (elements,'a) fold_method;
         fold_extends : (extend, 'a) fold_method; 
         fold_cargo : (behavior,'a) fold_method;
         fold_constraint : (constraint_,'a) fold_method;
         fold_der_spec : (der_spec,'a) fold_method;
         fold_enum_literal : (enum_literal,'a) fold_method;
         fold_algorithm : (algorithm,'a) fold_method;
         fold_external_def : (external_def,'a) fold_method;
         fold_texp : (texp,'a) fold_method;
         fold_exp : (exp,'a) fold_method;
         fold_exp_struct : (exp_struct,'a) fold_method;
         fold_attr : (attr,'a) fold_method;
         fold_idx : (idx,'a) fold_method;
         fold_statement_desc : (statement_desc,'a) fold_method;
         fold_statement : (statement,'a) fold_method;
         fold_equation_desc : (equation_desc,'a) fold_method;
         fold_equation : (equation,'a) fold_method;
         fold_modification : (modification,'a) fold_method;
         fold_type_redeclaration : (type_redeclaration,'a) fold_method;
         fold_component_redeclaration : (component_redeclaration,'a) fold_method;
         fold_component_modification : (component_modification,'a) fold_method;
         fold_component_modification_struct : (component_modification_struct,'a) fold_method;
         fold_modification_value : (modification_value,'a) fold_method;
         fold_name : (name,'a) fold_method;
         fold_named_arg : (named_arg,'a) fold_method;
         fold_identifier : (string,'a) fold_method;
         fold_comment_str : (string,'a) fold_method;
         fold_location : (Location.t,'a) fold_method;                              
       }  
                       
    let fold_id folder s a = a

    let fold_commented f this {commented; comment} a = let a' = f this commented a in
                                                       this.fold_comment this comment a'

    let fold_located f this {Location.txt;Location.loc} a = let a' = f this txt a in
                                                            this.fold_location this loc a'

    let fold_option f this o a = match o with
        Some x -> f this x a
      | None -> a
                  
    let rec fold_list f this l a = match l with
        [] -> a
      | hd::tl -> f this hd (fold_list f this tl a)

    let rec folds a = function
        [] -> a
      | tl::hd -> folds (tl a) hd

    let fold_for_loop f this {idx;body} = fold_list this.fold_idx this idx %> f this body

    let fold_else_conditional f this { guard ; elsethen } =
      this.fold_exp this guard %> f this elsethen
                                    
    let fold_conditional f this { condition ; then_ ; else_if ; else_ } =
      this.fold_exp this condition %>
        f this then_ %>
          fold_list (fold_else_conditional f) this else_if %>
            f this else_
  end
