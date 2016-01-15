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

open OUnit2
open Utils
open Batteries
open Syntax       
open Syntax_fragments

open Modlib
open Normalized
open Inter
    
open TestUtils
open P

(** Test case generator, checks the predicate on a path for a signature from source.
    The path is a singleton (def). 
    The predicate is abstracted over path to avoid tedious redundancy *)
let class_ input c pred =
  let path = Path.of_list [cm c] in
  (Printf.sprintf "Normalize '%s'" input) >:: (Parse.as_typedef **> Compute.signature **> Find.def_of path **> (pred path)) input

(** Test signatures directly *)
let signature desc input pred =
  desc >:: (Parse.as_typedef **> Compute.signature **> pred) input

(* Fixtures *)
open ClassValueFragments
let m_body source_path = {empty_object_struct with source_path; public = {empty_elements with fields = StrMap.singleton "x" {field_class=Real;field_binding=None; field_mod=StrMap.empty}}}

let class_M source_path = Class (m_body source_path)

let record_M source_path = Class {(m_body source_path) with object_sort = Record}

let class_with_public_M source_path = Class {empty_object_struct with source_path ; public = {
    empty_elements with class_members = StrMap.singleton "M" {empty_modified_class with class_ = class_M (DQ.snoc source_path (cm "M"))}}}
    
let class_with_protected_M source_path = Class {empty_object_struct with source_path ; protected = {empty_elements with class_members = StrMap.singleton "M" {empty_modified_class with class_ = class_M (DQ.snoc (DQ.snoc source_path `Protected) (cm "M"))}}}

let pol = Path.of_list 

(** Actual test cases *)
let test_cases = [
  class_ "type T = Real" "T"  (fun _ -> Is.class_value real_t) ;

  class_ "class M Real x; end M" "M" (fun p -> Is.class_value (class_M p));
  
  class_ "record M Real x; end M" "M" (fun p -> Is.class_value (record_M p));
  
  class_ "class A class M Real x; end M; end A" "A" (fun p -> Is.class_value (class_with_public_M p)) ;
  
  class_ "class A protected class M Real x; end M; end A" "A" (fun p -> Is.class_value (class_with_protected_M p)) ;

  class_ "record A end A" "A" (fun p -> Is.class_value (empty Record p)) ;

  signature
    "Normalization of replaceables"
    "class A class B replaceable type T = Real; end B; type T = B.T ; end A"
    ((Find.def_of (pol [cm "A"; cm "B"; cm "T"])) **> Is.replaceable **> (Is.class_value (type_ real))) ;

  signature
    "References to replaceables should yield dynamics"
    "class A class B replaceable type T = Integer; end B; type T = B.T ; end A"
    (Find.def_of (pol [cm "A" ; cm "T"]) **> (Is.class_value (type_ (dynref (pol [cm "A";cm "B";cm "T"]))))) ;

  signature
    "Forwarding Builtin Types"
    "class A type B = Real; class C type S = B; end C; end A"
    (Find.def_of (pol [cm "A"; cm "C" ; cm "S"]) **> Is.class_value real) ;

  signature
    "Forwarding of Imported Builtin Types"
    "class A type B = Real; class C import D = A.B; class E type F = D; end E; end C; end A"
    (Find.def_of (pol [cm "A"; cm "C"; cm "E"; cm "F"]) **> Is.class_value (type_ real));

  signature
    "Inheritance of forwarded Builtin Types"
    "class A class B1 type T = Real; end B1; extends B1; end A"
    (Find.def_of (pol [cm "A" ; sup 0; cm "T"]) **> Is.class_value real );

  signature
    "Inheritance of nested forwarded Builtin Types"
    "class A class B class C type T = Real; end C; end B; 
             class D extends B; end D; 
     end A" 
    (Find.def_of (pol [cm "A"; cm "D"; sup 0; cm "C"; cm "T"]) **> Is.class_value (type_ real)) ;

  signature
    "Inheritance of Fields"
    "class AA class B Real b; end B; 
              class C extends B; end C; end AA"
    (Find.def_of (pol [cm "AA"; cm "C"; sup 0; fld "b"]) **> Is.class_value Normalized.Real) ;

  signature
    "Lookup of redeclared Elements"
    "class A 
       class B2 
         replaceable type T2 = Real; 
       end B2; 
       class C = B2(redeclare type T2 = Integer); 
       type T = C.T2 ; 
     end A"
    (Find.def_of (pol [cm "A"; cm "T"]) (Is.replaceable (Is.class_value (type_ (int))))) ;

  signature
    "Lookup of indirectly redeclared elements"
    "class A3 
       model B3 
        replaceable type T3 = Integer; 
       end B3; 
       model C3 
        type T3 = Real; 
        model D3 = B3(redeclare type T3 = T3); 
       end C3; 
     end A3"
    (Find.def_of (pol [cm "A3"; cm "C3"; cm "D3"; cm "T3"]) **> (Is.replaceable (Is.class_value (type_ real)))) ;

  signature
    "Lookup of nested redeclarations"
    "class A4
       model B4
         replaceable type T = Integer;
       end B4;
       model C4
         B4 b;
       end C4;
       C4 c(b(redeclare type T = Real));
     end A4"
    (Find.def_of (pol [cm "A4"; fld "c" ; fld "b"; cm "T"]) **> Is.replaceable (Is.class_value (type_ real))) ;

  signature
    "Variability lookup"
    "class A5
       model B5
         constant Real x;
       end B5;
       model C5
         B5 b;
       end C5;
       C5 c(b(x = 3.0));
     end A5"
    (Find.def_of (pol [cm "A5"; fld "c" ; fld "b"; fld "x"]) **> Is.class_value (const (Normalized.Real))) ;

  signature
    "Lookup of Inheritied Fields with Variability"
    "class A6
       model B
         constant Real x;
       end B;
       model C
         extends B(x = 3.0);
       end C;
       C c;
     end A6"
    (Find.def_of (pol [cm "A6"; fld "c" ; sup 0; fld "x"]) **> (Is.class_value (const (Normalized.Real)))) ;
  
  signature
    "Redeclarations inside Components"
    "class A7
       model B
         replaceable type T = Integer;
       end B;
       model C
         B b;
       end C;
       model D
         extends C(b(redeclare type T = Real));
       end D;
       D d;
     end A7"
    (Find.def_of (pol [cm "A7"; fld "d" ; fld "b"; cl "T"]) **> Is.replaceable (Is.class_value (type_ real))) ;

  signature
    "Field Type Lookup"
    "class A8
       Real x(start = 2.0);
     end A8"
    (Find.def_of (pol [cm "A8"; fld "x"]) **> Is.class_value Normalized.Real) ;

  signature
    "Nested Field Lookup"
    "class A9
       model B Real x(start = 2.0); end B;
       B b(x(start = 42.0));
     end A9"
    (Find.def_of (pol [cm "A9" ; fld "b"; fld "x"]) **> Is.class_value Normalized.Real) ;

  signature
    "Indirect Field Type Redeclaration"
    "class A10
       model B replaceable type T = Integer; T x; end B;
       model C extends B(redeclare type T = Real); end C;
       C c;
     end A10"
    (Compute.structural_type_of (pol [cm "A10" ; fld "c"; sup 0; fld "x"]) **> Is.struct_val **>
     {sv_desc=Normalized.SReal; sv_attr={Normalized.empty_attr with fa_sort = Some Type}} ) ;
  
  signature
    "Nested Redeclaration inside Component"
    "class A11
       model B replaceable type T = Real; T x(start = 2.0); end B;
       model C type T = Integer; B b; end C;
       model D extends C(b(redeclare type T = T)); end D;
       D d;
     end A11"
    (* No superclass in lookup, modification of b in inheritance should yield a redeclared element directly *)
    (Find.def_of (pol [cm "A11" ; fld "d"; fld "b"; cl "T";]) **> Is.replaceable (Is.class_value int)) ;

  signature
    "Redeclare Extends Test"
    "class A12
       model B replaceable type T = Integer; end B;
       model C replaceable model B = B; end C;
       model D extends C; redeclare model extends B redeclare type T = Real; T t(start=0.0); end B; end D;    
     end A12"
    (Find.def_of (pol [cm "A12"; cl "D"; cl "B"; cl "T"]) **> Is.class_value real);

  (* Attempt to test a typical medium library pattern *)
  signature
    "Forwarding a Redeclaration into a Component (Media Library Pattern)"
    "package MiniMedium
       package DefaultMedium type T = Integer; end DefaultMedium ;
       package NonDefaultMedium type T = Real; end NonDefaultMedium;
       class Interface replaceable package Medium = DefaultMedium; end Interface;
       
       class SomeComponent extends Interface; constant Medium.T s = 42; end SomeComponent;
       
       class SomeModel extends Interface(redeclare package Medium = NonDefaultMedium); 
                       SomeComponent component(redeclare package Medium = Medium); 
       end SomeModel;
     end MiniMedium"
    (Compute.structural_type_of (pol [cm "MiniMedium"; cm "SomeModel"; fld "component"; cm "Medium"; cm "T"]) **>
     Is.struct_val **> {sv_desc=Normalized.SReal; sv_attr={Normalized.empty_attr with fa_sort = Some Type}}) ;
  
]

let suite = "Normalization" >::: test_cases
