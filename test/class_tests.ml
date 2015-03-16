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

open Utils
open Batteries
open Modelica_parser
open Syntax       
open Syntax.DefaultSyntax
open Syntax.Traversal       
open Syntax_fragments
open Modelica_lexer
open Location
open Parser_tests
open Report
open Motypes
open ClassNorm
open OUnit2
       
let assert_result = function
  | Failed -> assert_failure "Result was not OK."
  | Ok a -> a

let show_messages msgs =
  let s = IO.output_string () in
  Report.print_messages s msgs ; IO.close_out s
                        
let assert_normalization expected ast =
  let {final_messages; final_result} = normalize [ast] in
  IO.flush (!BatLog.output) ;
  let () = assert_equal ~msg:"No warnings and errors expected" ~printer:show_messages [] final_messages in (* TODO: filter warnings / errors *)
  let cv = assert_result final_result in  
  assert_equal ~msg:"equality of normalization result" ~printer:Normalized.show_object_struct expected cv
    
let class_ input expected =
  (Printf.sprintf "Normalize '%s'" input) >:: (parse_test td_parser input (assert_normalization expected))

open Normalized

let class_M = SimpleType (Class {empty_class_body with public = {empty_elements with dynamic_fields = StrMap.singleton "x" (SimpleType Real)}})
let class_with_public_M = SimpleType (Class {empty_class_body with public = {empty_elements with class_members = StrMap.singleton "M" class_M}})
let class_with_protected_M = SimpleType (Class {empty_class_body with protected = {empty_elements with class_members = StrMap.singleton "M" class_M}})
                                   
let test_cases = [
    class_ "type T = Real" {empty_class_body with public = {empty_elements with class_members = StrMap.singleton "T" (SimpleType Real)}} ;
    class_ "class M Real x; end M" {empty_class_body with public = {empty_elements with class_members = StrMap.singleton "M" class_M}} ;
    class_ "class A class M Real x; end M; end A" {empty_class_body with public = {empty_elements with class_members = StrMap.singleton "A" class_with_public_M}} ;
    class_ "class A protected class M Real x; end M; end A" {empty_class_body with public = {empty_elements with class_members = StrMap.singleton "A" class_with_protected_M}} ;

  ]
                                                
let suite = "Normalization" >::: test_cases
