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

module type S = sig
    module Syntax : Generic_syntax.S
    module Mapper : Mapper.S with module Syntax = Syntax
    module Folder : Folder.S with module Syntax = Syntax
                                                           
    open Syntax

    val default_folder : 'a Folder.folder

    val default_mapper : Mapper.mapper
                       
    module type TRAVERSAL = sig
        type sort

        val fold : (sort, 'a) Folder.fold_method
        val map : sort Mapper.map_method
      end
           
    module Unit : TRAVERSAL with type sort = unit_

    module DerSpec : TRAVERSAL with type sort = der_spec

    module Import : TRAVERSAL with type sort = import

    module Imports : TRAVERSAL with type sort = import list
                                             
    module Comment : TRAVERSAL with type sort = comment

    module Name : TRAVERSAL with type sort = name                   

    module TD : TRAVERSAL with type sort = typedef

    module TD_Desc : TRAVERSAL with type sort = typedef_desc
         
    module TRD : TRAVERSAL with type sort = type_redeclaration

    module CRD : TRAVERSAL with type sort = component_redeclaration 
                                              
    module CMOD : TRAVERSAL with type sort = component_modification
               
    module CMOD_Struct : TRAVERSAL with type sort = component_modification_struct

    module CMOD_Value : TRAVERSAL with type sort = modification_value
                       
    module Modification : TRAVERSAL with type sort = modification

    module Equation_Desc : TRAVERSAL with type sort = equation_desc               

    module Equation : TRAVERSAL with type sort = equation

    module Idx : TRAVERSAL with type sort = idx

    module Algorithm : TRAVERSAL with type sort = statement list

    module Statement : TRAVERSAL with type sort = statement

    module Statement_Desc : TRAVERSAL with type sort = statement_desc
                                                         
    module Named_Arg : TRAVERSAL with type sort = named_arg

    module Exp : TRAVERSAL with type sort = exp

    module Elements : TRAVERSAL with type sort = elements

    module Composition : TRAVERSAL with type sort = composition

    module Extension : TRAVERSAL with type sort = extension

    module Extend : TRAVERSAL with type sort = extend
  end

module Make(Tree : Generic_syntax.S) : S with module Syntax = Tree
