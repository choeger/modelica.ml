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
open Modelica_parser
open Syntax       
open Syntax_fragments
open Syntax_fragments
open Modelica_lexer
open Location
open Parser_tests
open Report

open Modlib
open Modlib.Inter
       
let assert_result = function
  | Failed -> assert_failure "Result was not OK."
  | Ok a -> a

let show_messages msgs =
  let s = IO.output_string () in
  Report.print_messages s msgs ; IO.close_out s


let assert_normalization expected td =  
  let parsed = {within = Some []; toplevel_defs = [td] } in
  let {final_messages; final_result} = Report.run (NormSig.norm_pkg_root (Trans.translate_pkg_root {root_units=[{FileSystem.scanned="testcase"; parsed}];root_packages=[]} )) {messages=[]; output=Normalized.empty_elements} in
  IO.flush (!BatLog.output) ;
  let () = assert_equal ~msg:"No warnings and errors expected" ~printer:show_messages [] final_messages in (* TODO: filter warnings / errors *)
  let cv = assert_result final_result in
  expected cv 

open Normalized
let cm = Modlib.Inter.Path.cm

let eq expected got = 
  assert_equal ~cmp:equal_class_value ~msg:(Printf.sprintf "equality of normalization result = %b" (expected = got)) ~printer:show_class_value (norm_cv expected) (norm_cv got)

let eq_val name expected normalized = eq (expected (Path.singleton (cm name))) (StrMap.find name normalized.class_members)

let should_be_replaceable expected got =
  match got with
    Replaceable v -> (expected v)
  | _ -> assert_failure ("Expected a replaceable type, got: " ^ (show_class_value got))

(* Lookup a name and apply a predicate *)
let rec lookup_ x xs f got =
  let m = try Normalized.follow_path_es got Name.empty got xs x
    with IllegalPath i -> Printf.eprintf "%s\n" (Normalized.show_elements_struct got) ; raise (IllegalPath i)
  in 
  match m with
  | `Found {found_value} ->
    begin match flat found_value with
        {flat_val = GlobalReference n; flat_attr} -> 
        begin match DQ.front n with
          (* In case of a global reference, lookup the reference and remember all local attributes *)
            Some (x,xs) -> let pipe = fun flat_val -> f (unflat {flat_val; flat_attr}) in
            lookup_ x xs pipe got 
          | None -> assert_failure
                      (Printf.sprintf "Empty global reference when looking up %s" (Inter.Path.show (DQ.cons x xs)))
        end
      (* In any other case, apply the predicate *)
      | _ -> f found_value
    end
  | _ as result -> assert_failure (Printf.sprintf "Could not find test-path.\n%s\n %s\n" (show_search_result result) (show_elements_struct got)) 

let lookup x xs f got =
  lookup_ x (DQ.of_list xs) f got

let lookup_cl x xs f got =
  lookup_ (`ClassMember x) (DQ.map (fun x -> `ClassMember x) (Name.of_list xs)) f got

let class_ input expected =
  (Printf.sprintf "Normalize '%s'" input) >:: (parse_test td_parser input (assert_normalization expected))

let m_body source_path = {empty_object_struct with source_path; public = {empty_elements with fields = StrMap.singleton "x" {field_class=Real;field_binding=None; field_mod=StrMap.empty}}}
let class_M source_path = Class (m_body source_path)
let record_M source_path = Class {(m_body source_path) with object_sort = Record}
let class_with_public_M source_path = Class {empty_object_struct with source_path ; public = {
    empty_elements with class_members = StrMap.singleton "M" (class_M (DQ.snoc source_path (cm "M")))}}
let class_with_protected_M source_path = Class {empty_object_struct with source_path ; protected = {empty_elements with class_members = StrMap.singleton "M" (class_M (DQ.snoc (DQ.snoc source_path `Protected) (cm "M")))}}

let empty object_sort source_path = (Class {empty_object_struct with object_sort; source_path })                                               
let type_ arg = Constr {constr=Sort Type; arg}
let const arg = Constr {constr=Var Constant; arg}
let real = type_ Real
let int = type_ Int
let real_t x = real
let replaceable t = Replaceable t

let sup n = `SuperClass n
let cl x = `ClassMember x
let fld x = `FieldType x
let cl_path xs = DQ.of_list (List.map cl xs)
let dynref x = DynamicReference x


let test_cases = [
  class_ "type T = Real" (eq_val "T" real_t ) ;
  class_ "class M Real x; end M" (eq_val "M" class_M);
  class_ "record M Real x; end M" (eq_val "M" record_M);
  class_ "class A class M Real x; end M; end A" (eq_val "A" class_with_public_M) ;
  class_ "class A protected class M Real x; end M; end A" (eq_val "A" class_with_protected_M) ;

  class_ "record A end A" (eq_val "A" (empty Record)) ;

  class_ "class A class B replaceable type T = Real; end B; type T = B.T ; end A" (lookup_cl "A" ["B"; "T"] (eq (replaceable (type_ real)))) ;

  class_ "class A class B replaceable type T = Integer; end B; type T = B.T ; end A" (lookup_cl "A" ["T"] (eq (type_ (dynref (cl_path ["A";"B";"T"]))))) ;


  class_ "class A type B = Real; class C type S = B; end C; end A" (lookup_cl "A" ["C";"S"] (eq (real))) ;

  class_ "class A type B = Real; class C import D = A.B; class E type F = D; end E; end C; end A" (lookup_cl "A" ["C"; "E";"F"] (eq (type_ real)));

  class_ "class A class B1 type T = Real; end B1; extends B1; end A"
    (lookup (cl "A") [sup 0 ; cl "T"] (eq (real)));

  class_ "class A class B class C type T = Real; end C; end B; 
            class D extends B; end D; end A"
    (lookup (cl "A") [cl "D"; sup 0; cl "C"; cl "T"] (eq (type_ real))) ;

  class_ "class AA class B Real b; end B; 
            class C extends B; end C; end AA"
    (lookup (cl "AA") [cl "C"; sup 0; fld "b"] (eq Normalized.Real)) ;

  class_ "class A 
              class B2 
                replaceable type T2 = Real; 
              end B2; 
              class C = B2(redeclare type T2 = Integer); 
              type T = C.T2 ; 
            end A"
    (lookup_cl "A" ["T"] (eq (replaceable (type_ (int))))) ;

  class_ "class A3 
              model B3 
                replaceable type T3 = Integer; 
              end B3; 
              model C3 
                type T3 = Real; 
                model D3 = B3(redeclare type T3 = T3); 
              end C3; 
            end A3"
    (lookup (cl "A3") [cl "C3"; cl "D3"; cl "T3"]
       (eq (replaceable (type_ real)))) ;

  class_ "class A4
              model B4
                replaceable type T = Integer;
              end B4;
              model C4
                B4 b;
              end C4;
              C4 c(b(redeclare type T = Real));
            end A4"
    (lookup (cl "A4") [fld "c" ; fld "b"; cl "T"] (eq (replaceable (type_ real)))) ;

  class_ "class A5
              model B5
                constant Real x;
              end B5;
              model C5
                B5 b;
              end C5;
              C5 c(b(x = 3.0));
            end A5"
    (lookup (cl "A5")
       [fld "c" ; fld "b"; fld "x"] (eq (const (Normalized.Real)))) ;

  class_ "class A6
              model B
                constant Real x;
              end B;
              model C
                extends B(x = 3.0);
              end C;
              C c;
            end A6"
    (lookup (cl "A6")
       [fld "c" ; sup 0; fld "x"] (eq (const (Normalized.Real)))) ;

  class_ "class A7
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
    (lookup (cl "A7") [fld "d" ; fld "b"; cl "T"] (eq (replaceable (type_ real)))) ;

  class_ "class A8
              Real x(start = 2.0);
            end A8"
    (lookup (cl "A8") [fld "x"] (eq Normalized.Real)) ;

  class_ "class A9
              model B Real x(start = 2.0); end B;
              B b(x(start = 42.0));
            end A9"
    (lookup (cl "A9") [fld "b"; fld "x"] (eq Normalized.Real)) ;

  class_ "class A10
              model B replaceable type T = Real; Real x(start = 2.0); end B;
              model C extends B(x(start=42.0),redeclare type T = Real); end C;
              C c;
            end A10"
    (lookup (cl "A10") [fld "c"; sup 0; fld "x"] (eq Normalized.Real)) ;

  class_ "class A11
            model B replaceable type T = Real; T x(start = 2.0); end B;
            model C type T = Integer; B b; end C;
            model D extends C(b(redeclare type T = T)); end D;
            D d;
          end A11"
    (* No superclass in lookup, modification of b in inheritance should yield a redeclared element directly *)
    (lookup (cl "A11") [fld "d"; fld "b"; cl "T";] (eq (replaceable int))) ;

  class_ "class A12
            model B replaceable type T = Integer; end B;
            model C replaceable model B = B; end C;
            model D extends C; redeclare model extends B redeclare type T = Real; T t(start=0.0); end B; end D;    
          end A12"
    (lookup (cl "A12") [cl "D"; cl "B"; cl "T"] (eq (real)));
  
]

let suite = "Normalization" >::: test_cases
