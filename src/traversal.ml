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

let default_folder = {
  fold_unit_ = Unit.fold ;
  fold_within = fold_id;
  fold_comment = fold_id;
  fold_annotation = fold_id;
  fold_typedef_options = fold_id;
  fold_typedef = fold_id;
  fold_composition = fold_id;
  fold_redeclared_typedef = fold_id;
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
