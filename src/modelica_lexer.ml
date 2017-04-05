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
open Batteries
open Utils       
type cursor = Location.t

open Location

type 'a loc = 'a Location.loc = {
  txt : 'a;
  loc : Location.t;
}

let show_location l =
  Location.print Format.str_formatter l ;
  Format.flush_str_formatter ()

type tokplus = token loc

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

(* Highlight the location by printing it again. *)
let highlight_dumb ppf lb loc =
  (* Char 0 is at offset -lb.lex_abs_pos in lb.lex_buffer. *)
  let pos0 = -lb.lex_abs_pos in
  (* Do nothing if the buffer does not contain the whole phrase. *)
  if pos0 < 0 then raise Exit;
  let end_pos = lb.lex_buffer_len - pos0 - 1 in
  (* Determine line numbers for the start and end points *)
  let line_start = ref 0 and line_end = ref 0 in
  for pos = 0 to end_pos do
    if Bytes.get lb.lex_buffer (pos + pos0) = '\n' then begin
      if loc.loc_start.pos_cnum > pos then incr line_start;
      if loc.loc_end.pos_cnum   > pos then incr line_end;
    end
  done;
  (* Print character location (useful for Emacs) *)
  Format.fprintf ppf "Characters %i-%i:@."
    loc.loc_start.pos_cnum loc.loc_end.pos_cnum;
  (* Print the input, underlining the location *)
  Format.pp_print_string ppf "  ";
  let line = ref 0 in
  let pos_at_bol = ref 0 in
  for pos = 0 to end_pos do
    match Bytes.get lb.lex_buffer (pos + pos0) with
    | '\n' ->
      if !line = !line_start && !line = !line_end then begin
        (* loc is on one line: underline location *)
        Format.fprintf ppf "@.  ";
        for _i = !pos_at_bol to loc.loc_start.pos_cnum - 1 do
          Format.pp_print_char ppf ' '
        done;
        for _i = loc.loc_start.pos_cnum to loc.loc_end.pos_cnum - 1 do
          Format.pp_print_char ppf '^'
        done
      end;
      if !line >= !line_start && !line <= !line_end then begin
        Format.fprintf ppf "@.";
        if pos < loc.loc_end.pos_cnum then Format.pp_print_string ppf "  "
      end;
      incr line;
      pos_at_bol := pos + 1
    | '\r' -> () (* discard *)
    | c ->
      if !line = !line_start && !line = !line_end then
        (* loc is on one line: print whole line *)
        Format.pp_print_char ppf c
      else if !line = !line_start then
        (* first line of multiline loc:
           print a dot for each char before loc_start *)
        if pos < loc.loc_start.pos_cnum then
          Format.pp_print_char ppf '.'
        else
          Format.pp_print_char ppf c
      else if !line = !line_end then
        (* last line of multiline loc: print a dot for each char
           after loc_end, even whitespaces *)
        if pos < loc.loc_end.pos_cnum then
          Format.pp_print_char ppf c
        else
          Format.pp_print_char ppf '.'
      else if !line > !line_start && !line < !line_end then
        (* intermediate line of multiline loc: print whole line *)
        Format.pp_print_char ppf c
  done

let digit = [%sedlex.regexp? '0'..'9']
let number = [%sedlex.regexp? Plus digit]
let letter = [%sedlex.regexp? 'a'..'z'|'A'..'Z']

let white_space = [%sedlex.regexp? 
                                   0x09 | 0x0b | 0x0c | 0x20 | 0x85 | 0xa0 | 0x1680 |
                                 0x2000 .. 0x200a | 0x2028 .. 0x2029 | 0x202f .. 0x202f | 0x205f .. 0x205f |
                                 0x3000 .. 0x3000 | 0xfeff]

let state_from_utf8_string src input = {
  buf = Utf8.from_string input ;
  src;
  m_cursor = { m_line = 1; m_bol = 0 ; m_last = None } ; 
  s_cursor = { str_start = 0 ; str_end = 0; str_bol = 0 ; str_line = 0 } }

let last_token { src; buf; m_cursor ; } = m_cursor.m_last

(* For strings containing multiple lines, we keep track of the positions on our own *)

let next_token ( { src ; buf ; m_cursor ;  s_cursor  } ) =

  let last_loc () =
    { pos_lnum = m_cursor.m_line ; pos_bol = m_cursor.m_bol ; 
      pos_cnum = lexeme_start buf ; pos_fname = src }
  in

  let lift txt =    
    let loc_start = match txt with      
        STRING(_) | QIDENT(_) ->
        let pos =
          { pos_lnum = m_cursor.m_line ; pos_bol = m_cursor.m_bol ;            
            pos_cnum = s_cursor.str_start ; pos_fname = src } in
        (* Parsed a string, Reset cursor *)
        m_cursor.m_line <- s_cursor.str_line;
        m_cursor.m_bol <- s_cursor.str_bol ;
        pos
      | _ -> last_loc ()
    in
    let loc_end = match txt with
      (* the only tokens that can span multiple lines are strings and quoted identifiers *)
        STRING(_) | QIDENT(_) -> { pos_lnum = s_cursor.str_line ; pos_bol = s_cursor.str_bol ; 
                                   pos_cnum = s_cursor.str_end ; pos_fname = src }
      | _ -> { loc_start with pos_cnum = lexeme_start buf + lexeme_length buf }
    in
    let tok = { txt ; loc = { loc_start ; loc_end ; loc_ghost = false } } 
    in
    m_cursor.m_last <- Some tok ; tok
  in

  let current _ = Utf8.lexeme buf in

  let newline () =
    m_cursor.m_line <- (m_cursor.m_line + 1) ;
    m_cursor.m_bol <- Sedlexing.lexeme_end buf ;
  in

  (* to regenerate using zsh: for N $KEYWORD_TOKEN; do echo "    | \"$N:l\" -> $N"; done | sort *)
  let ident_or_kw () = match (Sedlexing.Utf8.lexeme buf) with
    | "algorithm" -> ALGORITHM
    | "and" -> AND
    | "annotation" -> ANNOTATION
    | "assert" -> ASSERT
    | "block" -> BLOCK
    | "break" -> BREAK
    | "class" -> CLASS
    | "connector" -> CONNECTOR
    | "connect" -> CONNECT
    | "constant" -> CONSTANT
    | "constrainedby" -> CONSTRAINEDBY
    | "der" -> DER
    | "discrete" -> DISCRETE
    | "each" -> EACH
    | "else" -> ELSE
    | "elseif" -> ELSEIF
    | "elsewhen" -> ELSEWHEN
    | "encapsulated" -> ENCAPSULATED
    | "end" -> END
    | "enumeration" -> ENUMERATION
    | "equation" -> EQUATION
    | "expandable" -> EXPANDABLE
    | "extends" -> EXTENDS
    | "external" -> EXTERNAL
    | "false" -> FALSE
    | "final" -> FINAL
    | "flow" -> FLOW
    | "for" -> FOR
    | "function" -> FUNCTION
    | "if" -> IF
    | "import" -> IMPORT
    | "impure" -> IMPURE
    | "in" -> IN
    | "initial" -> INITIAL
    | "inner" -> INNER
    | "input" -> INPUT
    | "loop" -> LOOP
    | "model" -> MODEL
    | "not" -> NOT
    | "operator" -> OPERATOR
    | "or" -> OR
    | "outer" -> OUTER
    | "output" -> OUTPUT
    | "package" -> PACKAGE
    | "parameter" -> PARAMETER
    | "partial" -> PARTIAL
    | "protected" -> PROTECTED
    | "public" -> PUBLIC
    | "pure" -> PURE
    | "record" -> RECORD
    | "redeclare" -> REDECLARE
    | "replaceable" -> REPLACEABLE
    | "return" -> RETURN
    | "stream" -> STREAM
    | "then" -> THEN
    | "true" -> TRUE
    | "type" -> TYPE
    | "when" -> WHEN
    | "while" -> WHILE
    | "within" -> WITHIN
    |  _ as x -> IDENT (x)
  in

  let rec token () =
    match%sedlex buf with
    | "\r\n" -> newline () ; token ()
    | '\n' -> newline () ; token ()
    | '\r' -> newline () ; token ()
    | Plus ( white_space ) -> token ()
    | eof ->  ( EOF )

    | ":=" -> COLONEQ
    | ':' -> COLON
    | ',' -> COMMA
    | ';' -> SEMICOLON
    | '(' ->  LPAREN 
    | ')' ->  RPAREN
    | '{' -> LBRACE
    | '}' -> RBRACE
    | '=' ->  EQ
    | '^' -> POWER
    | ".^" -> DOTPOWER
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
    | '\'' -> s_cursor.str_start <- Sedlexing.lexeme_end buf ;  s_cursor.str_line <- m_cursor.m_line ; quoted_content (Text.of_char '\'')
    | '"' ->  s_cursor.str_start <- Sedlexing.lexeme_end buf ;  s_cursor.str_line <- m_cursor.m_line ; string_content Text.empty
    | number, '.', Opt( number ), Opt ( ('E' | 'e'), Opt('+' | '-'), number ) ->  ( FLOAT ( float_of_string (Sedlexing.Utf8.lexeme buf) ) )
    | number, ('e' | 'E'),  Opt('+' | '-'), number -> FLOAT ( float_of_string (Sedlexing.Utf8.lexeme buf) ) 
    | '.' ->  ( DOT )
    | number ->  ( INT ( int_of_string (current () ) ))

    | "//", Star ( Compl ('\n' | '\r') ) -> token ()
    | "/*" -> terminate_comment ()

    | (id_start | '_'), Star ( id_continue ) -> ident_or_kw () 
    | any ->
      failwith (Printf.sprintf "Lexical error in %s: Unexpected character '%s' (%d) at line %d column %d"
                  src
                  (Sedlexing.Utf8.lexeme buf) (Sedlexing.lexeme_char buf 0)
                  m_cursor.m_line m_cursor.m_bol)
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

  and string_content current =
    match %sedlex buf with
      '\\','\"' -> string_content (Text.append_char (UChar.of_char '"') current)
    | "\\?" -> string_content (Text.append_char (UChar.of_char '?') current)
    | "\\a" -> string_content (Text.append_char (UChar.of_char '\x07') current)
    | "\\b" -> string_content (Text.append_char (UChar.of_char '\x08') current)
    | "\\f" -> string_content (Text.append_char (UChar.of_char '\x0C') current)
    | "\\n" -> string_content (Text.append_char (UChar.of_char '\n') current)
    | "\\r" -> string_content (Text.append_char (UChar.of_char '\r') current)
    | "\\t" -> string_content (Text.append_char (UChar.of_char '\t') current)
    | "\\v" -> string_content (Text.append_char (UChar.of_char '\x0B') current)                              
    | "\\\\" -> string_content (Text.append_char (UChar.of_char '\\') current)                                                                              
    | "\r\n" | '\n' | '\r' ->  s_cursor.str_line <- (s_cursor.str_line + 1) ; s_cursor.str_bol <- Sedlexing.lexeme_end buf ; string_content (Text.append_char (UChar.of_char '\n') current) 
    | '"' -> s_cursor.str_end <- (Sedlexing.lexeme_end buf) - 1  ; STRING ( Text.to_string current )
    | eof -> EOF
    | any -> string_content (Text.append_char (UChar.of_int (Sedlexing.lexeme_char buf 0)) current)
    | _ -> failwith "no match on 'any'. This cannot happen"

  and quoted_content current =
    match %sedlex buf with
      "\\\'" -> quoted_content (Text.append_char (UChar.of_char '\'') current)
    | "\r\n" | '\n' | '\r' ->  s_cursor.str_line <- (s_cursor.str_line + 1) ; s_cursor.str_bol <- Sedlexing.lexeme_end buf ; quoted_content (Text.append_char (UChar.of_char '\n') current)  
    | '\'' -> s_cursor.str_end <- Sedlexing.lexeme_end buf ; IDENT ( Text.to_string (Text.append_char (UChar.of_char '\'') current) )
    | eof -> EOF
    | any -> quoted_content (Text.append_char (UChar.of_int (Sedlexing.lexeme_char buf 0)) current)
    | _ -> failwith "no match on 'any'. This cannot happen"                                                                 


  and merge { txt=t; loc } = match t with
      END -> begin
        let { m_line ; m_bol } = m_cursor in
        match token () with
          IF -> { txt = ENDIF ; loc = { loc with loc_end = last_loc () } }
        | FOR -> { txt = ENDFOR ; loc =  { loc with loc_end = last_loc () } }
        | WHILE -> { txt = ENDWHILE ; loc = { loc with loc_end = last_loc () } }
        | WHEN -> { txt = ENDWHEN ; loc = { loc with loc_end = last_loc () } }
        | IDENT(x) -> { txt = END_IDENT x; loc= { loc with loc_end = last_loc () } }
        | _ -> Sedlexing.rollback buf ; m_cursor.m_line <- m_line ; m_cursor.m_bol <- m_bol ; { txt=t; loc }
      end
    | INITIAL -> begin
        let { m_line ; m_bol } = m_cursor in
        match token () with
          EQUATION -> { txt = INITIAL_EQUATION ; loc = { loc with loc_end = last_loc () } }
        | ALGORITHM -> { txt = INITIAL_ALGORITHM ; loc = { loc with loc_end = last_loc () } }
        | _ -> Sedlexing.rollback buf ; m_cursor.m_line <- m_line ; m_cursor.m_bol <- m_bol ; { txt=t; loc }             
      end
    | _ -> { txt=t; loc }

  in merge (lift (token ()))
