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
open Batteries
open Modlib
open Utils
open Syntax

open Normalized
open NormImpl
open Class_tests
    
let assert_path lib path =
  match lookup_path lib path with
    `Found f -> f.found_value
  | `Recursion _ -> assert_failure "unexpected recursion"
  | (`PrefixFound _ | `NothingFound) as r -> assert_failure (Normalized.show_search_error r)
    
let assert_env path expected td =  
  let parsed = {within = Some []; toplevel_defs = [td] } in
  let {Report.final_messages; final_result} = Report.run (NormSig.norm_pkg_root (Trans.translate_pkg_root {root_units=[{FileSystem.scanned="testcase"; parsed}];root_packages=[]} )) {messages=[]; output=empty_elements} in
  IO.flush (!BatLog.output) ;
  let () = assert_equal ~msg:"No warnings and errors expected" ~printer:show_messages [] final_messages in (* TODO: filter warnings / errors *)
  let lib = assert_result final_result in
  let cl = assert_path lib path in
  assert_equal ~printer:show_environment expected (env lib cl)

let test_env descr input classname expected =
  descr >:: (Parser_tests.parse_test Parser.td_parser input (assert_env (Inter.Path.of_list classname) expected))


let test_cases = [
  test_env "Empty class" "class A end A" [`ClassMember "A"] NormImpl.empty_env ;

  test_env "Constant" "class A constant Real x = 42. ; end A" [`ClassMember "A"]
    {public_env=StrMap.of_list [("x", EnvField (const Real))]; protected_env=StrMap.empty} ;

  test_env "Protected Constant" "class A protected constant Real x = 42. ; end A" [`ClassMember "A"]
    {public_env=StrMap.empty; protected_env=StrMap.of_list [("x", EnvField (const Real))]} ;

  test_env "Type declaration" "class A type X = constant Real; end A" [`ClassMember "A"]
    {public_env=StrMap.of_list [("X", EnvField (const Real))]; protected_env=StrMap.empty} ;

  test_env "Inherited type declaration"
    "class A class B type X = constant Real; end B; class C extends B; end C; end A"
    [`ClassMember "A"; `ClassMember "C"]
    {public_env=StrMap.of_list [("X", EnvField (const Real))]; protected_env=StrMap.empty} ;
  
]

let suite = "Implementation Normalization" >::: test_cases

