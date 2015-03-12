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


(** Translation of Modelica type/class-expressions to classLang *)

open Ast.Flags
open Syntax
open Class_deps
open Utils
open Location
open Motypes
open Batteries
       
let attach_sort ct sort = PSort { rhs = ct ; defined_sort = sort }

let empty_class_hierarchy = { class_members = StrMap.empty ; fields = StrMap.empty ; super = [] }
                                
let rec translate_tds = function
  | Short tds -> (tds.td_name.txt, attach_sort (translate_texp tds.type_exp) tds.sort )
                               
  | Composition tds -> (tds.td_name.txt, translate_comp tds.sort tds.type_exp)
                            
  | Enumeration tds -> (tds.td_name.txt, attach_sort (PEnumeration (StrSet.of_list (List.map (fun {commented} -> commented) tds.type_exp))) tds.sort)
  | OpenEnumeration tds -> (tds.td_name.txt, attach_sort (PEnumeration (StrSet.empty)) tds.sort)
  | DerSpec tds -> (tds.td_name.txt, attach_sort (PDer tds.type_exp) tds.sort)
  | Extension tds ->
     let comp,mo = tds.type_exp in
     let ct = translate_comp tds.sort comp in
     match mo with Some m -> 
                   (tds.td_name.txt, translate_strict_redeclarations ct m)
                 | None -> (tds.td_name.txt, ct)

and translate_topdefs tds = PClass {public = {class_members = StrMap.of_enum (Enum.map translate_typedef (List.enum tds)); super=[]; fields=StrMap.empty}; protected = empty_class_hierarchy ; class_sort=Package}
                                   
and translate_typedef td = translate_tds td.commented
                                   
and translate_extends {ext_type} = translate_texp ext_type

and translate_def_struct 
    { def_name ; def_type ; def_constraint ; def_options } = let ct = translate_texp (match def_constraint with None -> def_type | Some cns -> cns.commented) in
                                                             (def_name, 
                                                              if def_options.replaceable then PReplaceable ct
                                                              else ct )
                                                  
and translate_def {commented} = translate_def_struct commented
                                                  
and translate_elements {extensions;typedefs;redeclared_types;defs;redeclared_defs} = 
  let super = List.map translate_extends extensions in
  let class_members = StrMap.of_enum (Enum.map translate_typedef (List.enum typedefs)) in
  let fields = StrMap.of_enum (Enum.map translate_def (List.enum defs)) in
  let type_redecls = List.map (fun td ->
                               let (rd_name, rd_rhs) = translate_typedef td in
                               ClassMember {rd_name ; rd_rhs }) redeclared_types
  in
  let field_redecls = List.map (fun d -> let (rd_name, rd_rhs) = translate_def d in
                                         Field {rd_name ; rd_rhs }) redeclared_defs
  in
  ({fields ; super; class_members}, (type_redecls @ field_redecls))
                             
and translate_comp class_sort { public ; protected; } =
  let (public, public_rds) = translate_elements public in
  let (protected, protected_rds) = translate_elements protected in
  let rds = public_rds @ protected_rds in
  let rd_lhs = PClass {public; protected; class_sort} in
  match rds with [] -> rd_lhs | _ -> Redeclaration {rds; rd_lhs}

and translate_strict_redeclarations rd_lhs {types} =
  StrictRedeclaration {rd_lhs ; rds = List.map (fun trd -> let rd_name = trd.redecl_type.commented.td_name.txt in
                                                           let rd_rhs  = translate_texp trd.redecl_type.commented.type_exp
                                                           in ClassMember {rd_name ; rd_rhs}) types}
    
and translate_texp = function
  | TName n -> Reference n
  | TRootName n -> RootReference n
                                 
  | TArray {base_type;dims} -> PArray {array_arg=translate_texp base_type; dimensions = List.length dims}
  | TMod {mod_type; modification} -> translate_strict_redeclarations (translate_texp mod_type) modification
  | TVar {flag;flagged} -> PVar {flagged = translate_texp flagged; flag}
  | TCon {flag;flagged} -> PCon {flagged = translate_texp flagged; flag}
  | TCau {flag;flagged} -> PCau {flagged = translate_texp flagged; flag}
