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

let ident = Syntax_fragments.any
let pol = Path.of_list 
let nol = Name.of_list
            
(** Test case generator, checks the predicate on a path for a signature from source.
    The path is a singleton (def). 
    The predicate is abstracted over path to avoid tedious redundancy *)
let class_ input c pred =
  (Printf.sprintf "Normalize '%s'" input) >:: (Parse.as_typedef **> Compute.signature **> (Find.def_of Path.empty [any c]) **>
                                               Is.successful **> The.lookup_result **> (pred (pol [cm c]))) input

(** Test signatures directly *)
let signature desc input pred =
  desc >:: (Parse.as_typedef **> Compute.signature **> pred) input

(* Fixtures *)
open ClassValueFragments
let m_body source_path = {empty_object_struct with source_path;
                                                   public = {empty_elements with fields = StrMap.singleton "x"
                                                                                     {field_pos=0; field_def=false;
                                                                                      field_class=Real;field_mod=no_modification}}}

let class_M source_path = Class (m_body source_path)

let record_M source_path = Class {(m_body source_path) with object_sort = Flags.Record}

let class_with_public_M source_path = Class {empty_object_struct with source_path ; public = {
    empty_elements with class_members = StrMap.singleton "M" {empty_modified_class with class_ = class_M (DQ.snoc source_path (cm "M"))}}}
    
let class_with_protected_M source_path = Class {empty_object_struct with source_path ; protected = {empty_elements with class_members = StrMap.singleton "M" {empty_modified_class with class_ = class_M (DQ.snoc (DQ.snoc source_path `Protected) (cm "M"))}}}

let class_def_of p cm k = Find.def_of p (List.map any cm) **> Is.successful **> The.lookup_result k

(** Actual test cases *)
let test_cases = [
  (class_ "type T = Real" "T"  (fun _ -> Is.class_value real_t) : OUnit2.test) ;

  class_ "replaceable type T = Real" "T"  (fun _ -> Is.replaceable **> Is.class_value real_t)  ;
  
  class_ "class M Real x; end M" "M" (fun p -> Is.class_value (class_M p));
  
  class_ "record M Real x; end M" "M" (fun p -> Is.class_value (record_M p));
  
  class_ "class A class M Real x; end M; end A" "A" (fun p -> Is.class_value (class_with_public_M p)) ;
  
  class_ "class A protected class M Real x; end M; end A" "A" (fun p -> Is.class_value (class_with_protected_M p)) ;

  class_ "record A end A" "A" (fun p -> Is.class_value (empty Flags.Record p)) ;

  signature
    "Normalization of replaceables"
    "class A class B replaceable type T = Real; end B; type T = B.T ; end A"
    ((class_def_of (pol [cm "A"; cm "B"]) ["T"]) **> Is.replaceable **> (Is.class_value (type_ real))) ;

  signature
    "References to replaceables should yield dynamics"
    "class A class B replaceable type T = Integer; end B; type T = B.T ; end A"
    (Find.type_at (pol [cm "A"; cm "T"]) **> (Is.class_value (type_ (dynref 0 (nol ["B"; "T"]))))) ;

  signature
    "Forwarding Builtin Types"
    "class A type B = Real; class C type S = B; end C; end A"
    (class_def_of (pol [cm "A"; cm "C" ]) ["S"] **> Is.class_value real_t) ;

  signature
    "Local Forwarding of Builtin Types"
    "replaceable class A type B = Real; B b; end A"
    (class_def_of (pol [cm "A"]) ["b"] **> Is.class_value real_t) ;  
  
  signature
    "Forwarding of Imported Builtin Types"
    "class A type B = Real; class C import D = A.B; class E type F = D; end E; end C; end A"
    (class_def_of (pol [cm "A"; cm "C"; cm "E"]) ["F"] **> Is.class_value (type_ real));

  signature
    "Shadowing of imports"
    "class A type S = Real; import T = A.S; class B type T = Integer; T x; end B; end A"
    (class_def_of (pol [cm "A"; cm "B"]) ["x"] **> Is.class_value (int_t));
  
  signature
    "Inheritance of forwarded Builtin Types"
    "class A class B1 type T = Real; end B1; extends B1; end A"
    (class_def_of (pol [cm "A"]) ["T"] **> Is.class_value real_t);

  signature
    "Inheritance of nested forwarded Builtin Types"
    "class A class B class C type T = Real; end C; end B; 
             class D extends B; end D; 
     end A" 
    (class_def_of (pol [cm "A"; cm "D"]) ["C"; "T"] **> Is.class_value (type_ real)) ;

  signature
    "Inheritance of Fields"
    "class AA class B Real b; end B; 
              class C extends B; end C; end AA"
    (class_def_of (pol [cm "AA"; cm "C"]) ["b"] **> Is.class_value Normalized.Real) ;

  signature
    "Scoped inheritance"
    "class A class B class C class F = D; end C; class D type T = Real; end D; end B; 
             class E extends B.C.F; type S = T; end E;
     end A"
    (class_def_of (pol [cm "A"; cm "E";]) ["S"] **> Is.class_value real_t) ;

  signature
    "Scoped nested inheritance"
    "class A class B type R = Real; class C class F = D; end C; class D type T = R; end D; end B; 
             class E extends B.C; class G extends F; type S = T; end G; end E;
     end A"
    (class_def_of (pol [cm "A"; cm "E"; cm "G"]) ["S"] **> Is.class_value real_t) ;
  
  signature
    "Lookup of redeclared Elements"
    "class A 
       class B2 
         replaceable type T2 = Real; 
       end B2; 
       class C = B2(redeclare type T2 = Integer); 
       type T = C.T2 ; 
     end A"
    (class_def_of (pol [cm "A"]) ["T"] (Is.replaceable (Is.class_value int_t))) ;

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
    (class_def_of (pol [cm "A3"; cm "C3"; cm "D3"]) ["T3"] **> (Is.replaceable (Is.class_value (type_ real)))) ;

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
    (Find.component (List.map any ["A4"; "c"; "b"; "T"]) **> Is.successful **> The.lookup_result **> Is.replaceable (Is.class_value (type_ real))) ;

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
    (Find.component (List.map any ["A5"; "c"; "b"; "x"]) **> Is.successful **> The.lookup_result  **> Is.class_value (const (Normalized.Real))) ;

  signature
    "Lookup of Inherited Fields with Variability"
    "class A6
       model B
         constant Real x;
       end B;
       model C
         extends B(x = 3.0);
       end C;
       C c;
     end A6"
    (class_def_of (pol [cm "A6"; cm "C"]) ["x"] **> (Is.class_value (const (Normalized.Real)))) ;
  
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
         type S = Real;
         extends C(b(redeclare type T = S));
       end D;
       D d;
     end A7"
    (Find.component (List.map any ["A7"; "d" ; "b"; "T"]) **> Is.successful **> The.lookup_result **> Is.replaceable (Is.class_value real_t)) ;

  signature
    "Field Type Lookup"
    "class A8
       Real x(start = 2.0);
     end A8"
    (class_def_of (pol [cm "A8"]) ["x"] **> Is.class_value Normalized.Real) ;

  signature
    "Nested Field Lookup"
    "class A9
       model B Real x(start = 2.0); end B;
       B b(x(start = 42.0));
     end A9"
    (Find.component (List.map any ["A9"; "b" ; "x"]) **> Is.successful **> The.lookup_result **> Is.class_value Normalized.Real) ;

(*  signature
    "Indirect Field Type Redeclaration"
    "class A10
       model B replaceable type T = Integer; T x; end B;
       model C extends B(redeclare type T = Real); end C;
       C c;
     end A10"
    (Compute.structural_type_of (pol [cm "A10" ; fld "c"; sup 0; fld "x"]) **> Is.struct_val **>
     {sv_desc=Normalized.SReal; sv_attr={Normalized.empty_attr with fa_sort = Some Type}} ) ;
*)
  
  signature
    "Nested Redeclaration inside Component"
    "class A11
       model B replaceable type T = Real; T x(start = 2.0); end B;
       model C type T = Integer; B b; end C;
       model D extends C(b(redeclare type T = T)); end D;
       D d;
     end A11"
    (Find.component (List.map any ["A11";"d";"b";"T"]) **> Is.successful **> The.lookup_result **> Is.replaceable (Is.class_value int_t)) ;

  signature
    "Redeclare Extends Test"
    "class A12
       model B replaceable type T = Integer; end B;
       model C replaceable model B = B; end C;
       model D extends C; redeclare model extends B redeclare type T = Real; T t(start=0.0); end B; end D;    
     end A12"
    (class_def_of (pol [cm "A12"; cl "D"; cl "B"]) ["T"] **> Is.class_value real_t);

  signature
    "Nested Redeclare Extends Test"
    "class A13
       model B replaceable type T = Integer; end B;
       model C replaceable model B = B; end C;
       model D extends C; redeclare model extends B type S = Real; end B; end D;
       model E extends D; redeclare model extends B redeclare type T = S; T t(start=0.0); end B; end E;           
     end A13"
    (class_def_of (pol [cm "A13"; cl "E"; cl "B"]) ["T"] **> Is.class_value real_t);
  
  (* Attempt to test a typical medium library pattern *)
    signature
    "Forwarding a Redeclaration into a Component (Media Library Pattern)"
    "package MiniMedium
       package DefaultMedium end DefaultMedium ;
       package NonDefaultMedium constant Real foo = 42.; end NonDefaultMedium;
       class Interface replaceable package Medium = DefaultMedium; end Interface;
       
       class SomeComponent extends Interface; Medium medium; end SomeComponent;
       
       class SomeModel extends Interface(redeclare package Medium = NonDefaultMedium); 
             SomeComponent component(redeclare package Medium = Medium, medium(foo = 23.)); 
       end SomeModel;
     end MiniMedium"
    (class_def_of (pol [cm "MiniMedium"; cm "SomeModel"]) ["component"; "medium"; "foo"] **> Is.constant **> Is.class_value real);
  
]

let suite = "Normalization" >::: test_cases
