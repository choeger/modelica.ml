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

open OUnit
open Modelica_parser
open Syntax
open Modelica_lexer

let expr_test input f =
  let ucs = state_from_utf8_string input in
  let next () = next_token ucs in
  let last () = last_token ucs in
  fun () ->
  try
    f (expr_parser "test" next last)
  with 
    SyntaxError e -> assert_failure (Printf.sprintf "Syntax Error at %s:\n%s" (show_location e) (error_message e input))

let expr input expected = 
  (Printf.sprintf "Parse '%s'" input) >::: [
    ("parsing" >::
       expr_test input (fun e -> assert_equal ~msg:"equality of parsed expression" (* ~printer:expr2str *) expected e ) ) ;
    (* ("re-parsing" >::
       expr_test input (fun e -> expr_test (expr2str ~max:100 e) (fun e -> assert_equal ~msg:"equality of re-parsed expression" ~printer:expr2str (prep_expr expected) (prep_expr e)) ())) ; *)
  ]
      
let test_cases = [ 
  expr "1.234" (Real(1.234));
  expr "x" (Ide("x")) ;
  expr "new_foo" (Ide "new_foo");
  expr "-1" (Int(-1));
  expr "x.bar" (Proj ({field = "bar"; object_=Ide("x") }));
]
						  
let suite = "Parser" >::: test_cases
