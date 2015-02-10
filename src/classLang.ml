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
open Class_deps
open Utils
open Location
       
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

 and value_hierarchy = { vfields : class_value_element StrMap.t ; vsuper : class_value list }
                               
 and class_value_element = { vkind : class_element_kind ; vbody : class_value }

type pointee_kind = SuperClass of int
                  | NamedElement of class_element_kind
                      
type ptr = { named : name ; pointee_kind : pointee_kind } 

let empty_hierarchy = Hierarchy {fields=StrMap.empty ; super = []}
             
let kindof e = function
    Syntax.Function | OperatorFunction -> { kind = Function ; body = e }
    | _ -> { kind = Static; body = e}
             
let rec translate_tds = function
  | Short tds -> (tds.td_name.txt,kindof (translate_texp tds.type_exp) tds.sort)
                               
  | Composition tds -> (tds.td_name.txt, kindof (translate_comp tds.type_exp) tds.sort)
                            
  | Enumeration tds -> (tds.td_name.txt,kindof (Primitive ("enumeration", [])) tds.sort) 
  | OpenEnumeration tds -> (tds.td_name.txt,kindof (Primitive ("open enumeration", [])) tds.sort)
  | DerSpec tds -> (tds.td_name.txt,kindof (Primitive ("derivative", [])) tds.sort)
  | Extension tds -> (tds.td_name.txt,kindof (Primitive ("extension", [])) tds.sort)

and translate_topdefs tds = Hierarchy {fields = StrMap.of_enum (Enum.map translate_typedef (List.enum tds)); super=[]}
                                   
and translate_typedef td = translate_tds td.commented
                                   
and translate_extends {ext_type} = translate_texp ext_type
                                   
and translate_elements {extensions;typedefs;redeclared_types} = 
  let super = List.map translate_extends extensions in
  let own_fields = Enum.map translate_typedef (List.enum typedefs) in
  let overloaded = Enum.map translate_typedef (List.enum redeclared_types) in
  {fields = StrMap.of_enum (Enum.concat (List.enum [own_fields;overloaded])) ; super }
  
and translate_comp { public ; protected; } =
  let public = translate_elements public in
  let protected = translate_elements protected in
  Hierarchy {fields = StrMap.union public.fields protected.fields ; super = public.super @ protected.super }

and translate_redeclarations {types} =
  StrMap.of_enum (Enum.map (fun trd -> translate_tds (Short trd.redecl_type.commented)) (List.enum types))
    
and translate_texp = function
  | TName n -> Reference n
  | TRootName n -> RootReference n
                                 
  | TArray {base_type} -> Primitive("Array", [translate_texp base_type])
  | TMod {mod_type; modification} -> Hierarchy {super=[translate_texp mod_type]; fields = translate_redeclarations modification}
  | TVar {flagged} -> Primitive ("Variability", [translate_texp flagged] )
  | TCon {flagged} -> Primitive ("Connectivity", [translate_texp flagged] )
  | TCau {flagged} -> Primitive ("Causality", [translate_texp flagged] )

exception ExpansionException 
            
let rec find_static_name e = function
    [] -> Some e
  | x::r -> begin match e.body with
                    Hierarchy {fields} ->
                    begin
                      match StrMap.Exceptionless.find x.txt fields with
                        None -> None
                      | Some e -> find_static_name e r
                    end
                  | _ -> None
            end
      
let expand c = function
    Path(p) -> begin match find_static_name c p with
                 Some {kind;body} -> [({named = p; pointee_kind = NamedElement kind}, body)]
               | None -> raise ExpansionException
               end
  | Superclass(p) ->
     begin match find_static_name c p with
             Some {body=Hierarchy {fields ; super}} -> List.mapi (fun i s -> ({named = p; pointee_kind = SuperClass i},s)) super
           | _ -> raise ExpansionException
     end

(*
exception DereferenceException
       
let rec add c c' = function
    {named = []; pointee_kind = NamedElement kind} -> {body = c'; kind }

  | {named = []; pointee_kind = SuperClass i} -> begin match c.body with
                                                         Hierarchy {fields; super} when List.length super = i -> {c with body = Hierarchy {fields; super=c'::super}}
                                                       | _ -> raise DereferenceException
                                                 end
                                          
  | {named = x::r; pointee_kind} -> begin match c.body with                                                     
                                          | Hierarchy {fields;super} ->
                                             let c'' = add (StrMap.find_or_else {body = empty_hierarchy; kind = Static} x.txt fields) c' {named=r; pointee_kind} in
                                             {c with body = Hierarchy {fields=StrMap.add x.txt c'' fields; super}}
                                          | _ -> raise DereferenceException                                                                           
                                   end
                                 *)
exception CannotNormalize of name                                      
                                      
let rec normalize = function
    Hierarchy {fields;super} -> VHierarchy {vfields = StrMap.map normalize_element fields; vsuper = List.map normalize super}
  | Primitive (x, cs) -> VPrimitive (x, List.map normalize cs)
  | Method xs -> VMethod xs
  | Reference name -> raise (CannotNormalize name)
  | RootReference name -> raise (CannotNormalize name)

and normalize_element {kind;body} = {vkind=kind; vbody=normalize body}
    
                                
type prefix_found = { found : name ; not_found : str }
                           
type lookup_result = Found of class_value_element
                   | NothingFound
                   | PrefixFound of prefix_found

type unresolved_dependency = { searching : name ; dependency : kontext_label }
                                      
exception UnresolvedDependency of unresolved_dependency
                                      
let rec get_element e = function    
    [] -> Found e            
  | x::xs -> begin
      match e.vbody with
      | VHierarchy {vfields;vsuper} -> if StrMap.mem x.txt vfields then Found (StrMap.find x.txt vfields) else
                                         pickfirst (x::xs) vsuper
      (* TODO: methods *)
      | _ -> NothingFound
    end

and pickfirst name = function
    [] -> NothingFound
  | v::vs -> begin match get_element {vkind = Static ; vbody = v} name with
                     NothingFound -> pickfirst name vs
                   | _ as r -> r
             end
                           
and lookup e prefix suffix = function
    [] -> NothingFound
  | {source_label=(Superclass p)} :: srcs ->
     begin
       match get_element e p with
       | Found e' -> begin
           match get_element e' (prefix::suffix) with
           | NothingFound -> lookup e prefix suffix srcs
           | r -> r
         end
         | _ -> raise (UnresolvedDependency { searching = prefix::suffix ; dependency = Superclass p })
     end
  | {source_label=Path(p)} :: _ ->
     begin
       match get_element e p with
       | Found e' -> begin match get_element e' suffix with NothingFound -> PrefixFound { found = [prefix]; not_found = List.hd suffix } | r -> r end
       | _ -> raise (UnresolvedDependency { searching = prefix::suffix ; dependency = Path p })
     end

let start_lookup v scope prefix suffix =
  let sources = search_scope prefix [] scope in
  lookup v prefix suffix sources
                           
let eval v scope (ptr,c') = match c' with
    Reference (x::xs) -> start_lookup v scope x xs
  | Reference [] -> raise Syntax_fragments.EmptyName
  | RootReference name -> get_element v name
  |  _ -> Found {vkind=(match ptr.pointee_kind with SuperClass _ -> Static | NamedElement k -> k); vbody=(normalize c')}
  
  
  
