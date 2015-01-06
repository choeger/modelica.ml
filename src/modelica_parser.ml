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

open Modelica_lexer
open Lexing
open Location
       
let get_token {token} = token 

let get_start src {cursor} = cursor.loc_start

let get_end src {cursor} = cursor.loc_end

exception SyntaxError of cursor
                           
open Batteries

let locate = function
    Some ( {cursor} ) ->  cursor
  | None -> { loc_start = dummy_pos ; loc_end = dummy_pos ; loc_ghost = true }

let guard parser next last = try parser next  
                             with
                             | Generated_parser.Error -> raise ( SyntaxError ( locate (last ()) ) )

(* entry points below stored definition, mainly for unit tests *)
let texpr_parser src = guard (MenhirLib.Convert.traditional2revised get_token (get_start src) (get_end src) Generated_parser.modelica_texpr)

let expr_parser src = guard (MenhirLib.Convert.traditional2revised get_token (get_start src) (get_end src) Generated_parser.modelica_expr)

let stmt_parser src = guard (MenhirLib.Convert.traditional2revised get_token (get_start src) (get_end src) Generated_parser.modelica_stmt)

let eq_parser src = guard (MenhirLib.Convert.traditional2revised get_token (get_start src) (get_end src) Generated_parser.modelica_eq)

let import_parser src = guard (MenhirLib.Convert.traditional2revised get_token (get_start src) (get_end src) Generated_parser.modelica_import)

let extends_parser src = guard (MenhirLib.Convert.traditional2revised get_token (get_start src) (get_end src) Generated_parser.modelica_extends)

let defs_parser src = guard (MenhirLib.Convert.traditional2revised get_token (get_start src) (get_end src) Generated_parser.modelica_definitions)

let td_parser src = guard (MenhirLib.Convert.traditional2revised get_token (get_start src) (get_end src) Generated_parser.modelica_type_definition)

let unit_parser src = guard (MenhirLib.Convert.traditional2revised get_token (get_start src) (get_end src) Generated_parser.modelica_stored_definition)
                          
let error_message e input =
  let lb = Lexing.from_string (input ^ "\n") in
  highlight_dumb Format.str_formatter lb e ; Format.flush_str_formatter ()
