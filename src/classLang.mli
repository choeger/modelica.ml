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
open Class_deps
open Utils

       
type class_ = Hierarchy of hierarchy
            | Reference of name
            | RootReference of name
            | Primitive of string * (class_ list)
            | Method of string list
                               
 and hierarchy = { fields : class_element StrMap.t ; super : class_ list }

 and class_element = { kind : class_element_kind ; body : class_ }

 and class_element_kind = Static
                        | Replaceable
                        | Function
type t = class_

type class_value = VHierarchy of value_hierarchy
                 | VPrimitive of string * class_value list
                 | VMethod of string list
                 | VDelayed of delayed_value

 and delayed_value = { environment : scope ; expression : class_ ; def_label:name}
                                     
 and value_hierarchy = { vfields : class_value_element StrMap.t ; vsuper : class_value list }
                               
 and class_value_element = { vkind : class_element_kind ; vbody : class_value }
                            
val empty_hierarchy : value_hierarchy

val value_hierarchy_to_yojson : value_hierarchy -> Yojson.Safe.json
                        
type unresolved_dependency = { searching : name ; dependency : kontext_label }
                                      
exception UnresolvedDependency of unresolved_dependency
             
val translate_topdefs : typedef list -> t

val normalize : typedef -> value_hierarchy
