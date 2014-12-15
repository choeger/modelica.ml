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

open Lexing
open Generated_parser
open Sedlexing
       
type cursor = { start : position ; end_ : position }

type tokplus = {
  token : token;
  cursor : cursor ;
}

type m_cursor = {
  mutable m_line : int;
  mutable m_bol : int;
  mutable m_last : tokplus option;
}

type str_cursor = {
  mutable str_start : int ;
  mutable str_end : int ;
  mutable str_line : int ;
  mutable str_bol : int ;
}
                  
type lexer_state = {
  src : string ;
  buf : lexbuf;
  m_cursor : m_cursor ;
  s_cursor : str_cursor ;
}

let digit = [%sedlex.regexp? '0'..'9']
let number = [%sedlex.regexp? Plus digit]
let letter = [%sedlex.regexp? 'a'..'z'|'A'..'Z']

let white_space = [%sedlex.regexp? 
                   0x09 | 0x0b | 0x0c | 0x20 | 0x85 | 0xa0 | 0x1680 |
                   0x2000 .. 0x200a | 0x2028 .. 0x2029 | 0x202f.. 0x202f | 0x205f.. 0x205f |
                   0x3000.. 0x3000]

let state_from_utf8_string input = {
  buf = Utf8.from_string input ;
  src = "test input" ; 
  m_cursor = { m_line = 0; m_bol = 0 ; m_last = None } ; 
  s_cursor = { str_start = 0 ; str_end = 0; str_bol = 0 ; str_line = 0 } }
                                                  
let last_token { src; buf; m_cursor ; } = m_cursor.m_last

(* For strings containing multiple lines, we keep track of the positions on our own *)
                                          
let next_token ( { src ; buf ; m_cursor ;  s_cursor  } ) =
  
  let lift token =
    let start = match token with
        STRING(_) -> { pos_lnum = m_cursor.m_line ; pos_bol = m_cursor.m_bol ; 
		       pos_cnum = s_cursor.str_start ; pos_fname = src }
      | _ -> { pos_lnum = m_cursor.m_line ; pos_bol = m_cursor.m_bol ; 
	       pos_cnum = lexeme_start buf ; pos_fname = src }
    in
    let end_ = match token with
        (* the only token that can span multiple lines is the string *)
        STRING(s) -> { pos_lnum = s_cursor.str_line ; pos_bol = s_cursor.str_bol ; 
		       pos_cnum = s_cursor.str_end ; pos_fname = src }
      | _ -> { start with pos_cnum = lexeme_start buf + lexeme_length buf }
    in     
    let tok = { token ; cursor = { start ; end_ ; } } 
    in m_cursor.m_last <- Some tok ; tok
  in

  let current _ = Utf8.lexeme buf in

  let newline () =
    m_cursor.m_line <- (m_cursor.m_line + 1) ;
    m_cursor.m_bol <- Sedlexing.lexeme_end buf ;
  in
  
  let ident_or_kw () = match (Sedlexing.Utf8.lexeme buf) with
    |  _ as x -> IDENT (x)
  in

  let rec token () =
    match%sedlex buf with
    | "\r\n" -> newline () ; token ()
    | '\n' -> newline () ; token ()
    | '\r' -> newline () ; token ()
    | Plus ( white_space ) -> token ()
    | eof ->  ( EOF )

    | ',' -> COMMA
    | ';' -> SEMICOLON
    | '(' ->  LPAREN 
    | ')' ->  RPAREN
    | '{' -> LBRACE
    | '}' -> RBRACE
    | '=' ->  EQ
    | '+' ->  PLUS
    | '*' ->  TIMES
    | '/' ->  DIV
    | '-' ->  MINUS
    | ".+" ->  DOTPLUS
    | ".*" ->  DOTTIMES
    | "./" ->  DOTDIV
    | ".-" ->  DOTMINUS
    | '>' ->  GT
    | '<' ->  LT
    | ">=" -> GEQ
    | "<=" -> LEQ
    | "<>" -> NEQ
    | "==" -> EQEQ
    | '[' ->  LBRACKET 
    | ']' ->  RBRACKET
    | '"' ->  s_cursor.str_start <- Sedlexing.lexeme_end buf ;  s_cursor.str_line <- m_cursor.m_line ; string_content ()
    | Opt('-'), number, '.', Opt( number ), Opt ( 'e', Opt('+' | '-'), number ) ->  ( FLOAT ( float_of_string (Sedlexing.Utf8.lexeme buf) ) )
    | '.' ->  ( DOT )
    | Opt('-'), number ->  ( INT ( int_of_string (current () ) ))

    | "/*" -> terminate_comment ()

    | (id_start | '_'), Star ( id_continue | '\'' ) -> ident_or_kw () 
    | any -> failwith (Printf.sprintf "Unexpected character '%s'" (Sedlexing.Utf8.lexeme buf))
    | _ -> failwith "no match on 'any'. This cannot happen"
					  
  and terminate_comment () = 
    match %sedlex buf with
    | "*/" ->  token ()
    | "\r\n" ->  newline () ; terminate_comment ()                                   
    | '\n' ->  newline () ;  terminate_comment ()
    | '\r' ->  newline () ;  terminate_comment ()
    | eof -> EOF
    | any -> terminate_comment ()
    | _ -> failwith "no match on 'any'. This cannot happen"

  and string_content () =
    match %sedlex buf with
      "\\\"" -> string_content ()
    | "\r\n" | '\n' | '\r' ->  s_cursor.str_line <- (s_cursor.str_line + 1) ; s_cursor.str_bol <- Sedlexing.lexeme_end buf ; string_content () 
    | '"' -> s_cursor.str_end <- Sedlexing.lexeme_end buf ; STRING ( Sedlexing.Utf8.sub_lexeme buf s_cursor.str_start s_cursor.str_end )
    | eof -> EOF
    | any -> string_content ()
    | _ -> failwith "no match on 'any'. This cannot happen"
                            
                                                                 
  in lift (token ())
