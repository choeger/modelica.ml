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

(** This module contains dependency analysis for type evaluation (i.e. superclass resolution) of 
    a Modelica Model/Package *)

open Utils
open Syntax

type outside_superclass = {extended:str; parent:name}
(** A superclass that lies outside its own scope (i.e. as in the 'redeclare class extends ... ' mechanism *)
                            
type kontext_label = Path of name
                   | Superclass of name
                   | OutsideSuperclass of outside_superclass
(** A kontext label (kontext means a type-with-a-hole 
    and needs to be distinguished from the context used 
    during evaluation) is a basically a pointer to a 
    place in a type-tree, where a path needs to be looked up.
    In theory, there are multiple 𝛴-entries possible, but for
    implementation purposes it shouldn't matter in which order they
    are evaluated (as they are specified to be independent of each other).
 *) 

module LabelMap : Map.S with type key = kontext_label                                     

val name2str : name -> string

val label2str : kontext_label -> string
                                          
type dependency_source = {
  source_label : kontext_label;
  required_elements : name;
}
(** The source of a dependency is a kontext label together with a 
    (possibly empty) list of fields that need lookup. When this list
    is non-empty, the kontext-label should either point to a superclass
    or the dependency cannot be fulfilled anyway. *)                           

type dependency = {
  local_name : string;
  from : dependency_source list;
}
(** A dependency is a set of possible sources for a local name *)


type scope_entry = {
  scope_name : name ;
  scope_tainted: bool;
  scope_entries :  str StrMap.t;
}
(** A scope entry is a named area in the source code, where type-definitions can be found.
    A scope is tainted, when the corresponding class contains an extends-clause.
    It is also tainted, when it contains unqualified (i.e. ".*"-style) imports. Such
    imports not fully supported, though.
    The entries of a scope_entries are the (possibly locally renamed) lexically defined entities. 
 *) 

type scope = scope_entry list
(** The scope is a list of scope entries (in lookup order to allow for lexical shadowing). *)

val pp_scope : Format.formatter -> scope -> unit                         
val scope_to_yojson : scope -> Yojson.Safe.json
val scope_of_yojson : Yojson.Safe.json -> [`Ok of scope | `Error of string]
                         
type lexical_typedef = {
    kontext_label : kontext_label;
    scope : scope;
    dependencies : dependency list;
}
(** A lexical type-definition is identified by its kontext label and 
    contains a set of dependencies. *) 
                    
val search_scope : str -> name -> scope -> dependency_source list
(** Find all possible global names of a given identifier in the given scope *)
              
val scan_dependencies : scope -> typedef list -> lexical_typedef list
(** Create a list of lexical type definitions from a type definition AST for dependency analysis *)
                                                            
val topological_order : lexical_typedef list -> kontext_label list list
(** Sort the found kontext labels topological in dependency order *)

val builtin : string -> bool
(** Check if the given name is a builtin type in Modelica *)
