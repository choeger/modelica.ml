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

type position = Lexing.position = {
      pos_fname : string;
      pos_lnum : int;
      pos_bol : int;
      pos_cnum : int;
    } [@@deriving yojson]

type location = Location.t = {
      loc_start: position;
      loc_end: position;
      loc_ghost: bool;
    } [@@deriving yojson]
      
type 'a loc = 'a Location.loc = { txt : 'a; loc : location; } [@@deriving yojson]

type token =
 GT | LT | NEQ | GEQ | LEQ | EQ | EQEQ | LPAREN | RPAREN | LBRACKET | RBRACKET | LBRACE | RBRACE | SEMICOLON | COMMA | DOT | COLON | COLONEQ
 | INT of int
 | FLOAT of float
 | IDENT of string
 | QIDENT of string
 | STRING of string
 | DOTPOWER | POWER | PLUS | MINUS | TIMES | DIV | DOTPLUS | DOTMINUS | DOTTIMES | DOTDIV
 | EOF
 | ALGORITHM | DISCRETE | FALSE | LOOP | PURE | AND | EACH | FINAL | MODEL | RECORD | ANNOTATION | ELSE
 | FLOW | NOT | REDECLARE | ASSERT | ELSEIF | FOR | OPERATOR | REPLACEABLE | BLOCK | ELSEWHEN | FUNCTION | OR | RETURN
 | BREAK | ENCAPSULATED | IF | OUTER | STREAM | CLASS | END | IMPORT | OUTPUT | THEN | CONNECT | ENUMERATION | IMPURE
 | PACKAGE | TRUE | CONNECTOR | EQUATION | IN | PARAMETER | TYPE | CONSTANT | EXPANDABLE | INITIAL | PARTIAL | WHEN
 | CONSTRAINEDBY | EXTENDS | INNER | PROTECTED | WHILE | DER | EXTERNAL | INPUT | PUBLIC | WITHIN
 | ENDWHEN | ENDIF | ENDFOR | ENDWHILE | END_IDENT of string | INITIAL_EQUATION | INITIAL_ALGORITHM
                                [@@deriving show]

module StdFormat = Format
open Batteries

module StrMap = struct include Map.Make(String)
                       let union m1 m2 = Enum.fold (fun m (k,v) -> add k v m) m1 (enum m2)
                       let find_or_else v x m = if mem x m then find x m else v
                       let to_yojson a m = `Assoc (List.map (fun (k,v) -> (k,a v)) (bindings m))
                       let of_yojson js f = (`Error "Not yet implemented")
                       open StdFormat 
                       let pp pp_v fmt s = let pp_comma fmt () = fprintf fmt "," in
                                           let pp_pair fmt (k,v) = fprintf fmt "%s@ =@ %a" k pp_v v in
                                           fprintf fmt "@[{%a}@]" (pp_print_list ~pp_sep:pp_comma pp_pair) (bindings s)
                end
module StrSet = struct include Set.Make(String) 
                       let to_yojson s = `List (List.map (fun e -> `String e) (elements s))
                       let of_yojson js = (`Error "Not yet implemented")
                       open StdFormat
                       let pp fmt s = let pp_comma fmt () = fprintf fmt "," in fprintf fmt "@[{%a}@]" (pp_print_list ~pp_sep:pp_comma pp_print_string) (elements s)
                end
                        
module List = List


let unloc {Location.txt} = txt

let lunloc xs = List.map unloc xs
