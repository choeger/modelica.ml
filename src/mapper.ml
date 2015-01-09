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

(** {2 A generic Syntax mapper inspired by OCaml's Ast_mapper } *)

open Batteries
open Syntax
       
(** A mapper record implements one "method" per syntactic category,
    using an open recursion style: each method takes as its first
    argument the mapper to be applied to children in the syntax
    tree. *)
type mapper = {
  unit_ : mapper -> unit_ -> unit_ ;
  within : mapper -> name option -> name option ;
  comment : mapper -> comment -> comment ;              

  typedef_options : mapper -> typedef_options -> typedef_options;
  typedef : mapper -> typedef -> typedef;

  composition : mapper -> composition -> composition;

  redeclared_typedef : mapper -> typedef -> typedef;
  extension : mapper -> extension -> extension ;
  
  def : mapper -> definition -> definition ;
  redeclared_def : mapper -> definition -> definition ;

  import : mapper -> import -> import ;
  import_desc : mapper -> import_desc -> import_desc ;
  extend : mapper -> extend -> extend;
  
  imports : mapper -> import list -> import list ;
  public : mapper -> elements -> elements ;
  protected : mapper -> elements -> elements ;
  cargo : mapper -> behavior -> behavior ;

  constraint_ : mapper -> constraint_ -> constraint_ ;

  der_spec : mapper -> der_spec -> der_spec;
  
  enum_literal : mapper -> enum_literal -> enum_literal ;
  
  algorithm : mapper -> algorithm -> algorithm ;
  external_def : mapper -> external_def -> external_def ;

  texp : mapper -> texp -> texp ;
  exp : mapper -> exp -> exp;
                             
  statement : mapper -> statement -> statement;
  equation_desc : mapper -> equation_desc -> equation_desc;
  equation : mapper -> equation -> equation ;

  name : mapper -> name -> name ;
  str : mapper -> str -> str ;
}  

(** Lift a sub-map function to a map function over lists *)
let map_list sub this = List.map (sub this)

let map_commented sub this {commented; comment} = { commented = sub this commented ;
                                                    comment = this.comment this comment }
                                 
(** The identity map function. Does {b no} traversal *)
let id this x = x
                                 
(** Map for type-definitions *)                
module TD = struct
  let map_tds this sub { td_name ; sort ; type_exp ; cns ; type_options } =
    let type_options = this.typedef_options this type_options in
    let type_exp = sub this type_exp in
    let cns = Option.map (this.constraint_ this) cns in
    { td_name ; sort ; type_exp ; cns ; type_options }

  let map_desc this = function
      Short tds -> Short (map_tds this this.texp tds)
    | Composition tds -> Composition (map_tds this this.composition tds)
    | Extension tds -> Extension (map_tds this this.extension tds)
    | Enumeration tds -> Enumeration (map_tds this (map_list this.enum_literal) tds)
    | OpenEnumeration tds -> OpenEnumeration (map_tds this id tds)       
    | DerSpec tds -> DerSpec (map_tds this this.der_spec tds)
                                                         
  let map = map_commented map_desc

end

module Unit = struct              
  let map this { within; toplevel_defs; } = { within = this.within this within ;
                                              toplevel_defs = map_list this.typedef this toplevel_defs }
end

module DerSpec = struct
  let map this { der_name ; idents } =
    { der_name = this.name this der_name ;
      idents = map_list this.str this idents } 
end

module Name = struct
  let map this = map_list this.str this
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
                
let default_mapper = {
  unit_ = Unit.map ;
  within = id;

  typedef_options = id;
  typedef = TD.map;

  composition = id;

  redeclared_typedef = id;
  extension = id;
  
  def = id;
  redeclared_def = id;

  import_desc = Import_Desc.map ;
  import = Import.map;
  extend = id;
  
  imports = id;
  public = id;
  protected = id;
  cargo = id;

  constraint_ = id;

  der_spec = DerSpec.map;
  
  enum_literal = id;
  
  algorithm = id;
  external_def = id;

  texp = id;

  comment = id;

  exp = id;
  statement = id;

  equation_desc = id;
  equation = id;

  name = Name.map ;
  str = id;
};

