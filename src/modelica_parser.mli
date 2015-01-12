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

(** Parsers for different parts of the Modelica Syntax. *)

exception SyntaxError of Location.t

val error_message : Location.t -> string -> string
                           
type 'a parser = (unit -> Modelica_lexer.tokplus) -> (unit -> Modelica_lexer.tokplus option) -> 'a
(** A parser is a function that takes two token generators and yields a piece of abstract syntax. 
    The first token generator yields the next token from the input and the second yields the last token 
    that has been delivered, or [None], if no token has been delivered so far. The second generator is
    only used for error reporting (it is expected to yield the last token that has been looked at by the 
    LR(1) parser).
*)
                                                                                              
val texpr_parser : Syntax.texp parser 
(** Parser for type-expressions 
    @raise SyntaxError on syntax-error
*)
                               
val expr_parser : Syntax.exp parser 
(** Parser for expressions
    @raise SyntaxError on syntax-error
*)
                               
val stmt_parser : Syntax.statement parser
(** Parser for statements
    @raise SyntaxError on syntax-error
*)

val eq_parser : Syntax.equation parser
(** Parser for equations
    @raise SyntaxError on syntax-error
*)

val import_parser : Syntax.import parser
(** Parser for [import]-clauses 
    @raise SyntaxError on syntax-error
*)

val extends_parser : Syntax.extend parser
(** Parser for [extends]-clauses     
    @raise SyntaxError on syntax-error
*)
                                   
val defs_parser : (Syntax.definition list) parser
(** Parser for component definitions. Will expand definition lists 
    (i.e. [parameter Real x,y;] will generate abstract syntax equivalent to  
    [parameter Real x; parameter Real y;])
    @raise SyntaxError on syntax-error
*)

val td_parser : Syntax.typedef parser
(** Parser for type-definitions 
    @raise SyntaxError on syntax-error
*)
                               
val unit_parser : Syntax.unit_ parser
(** Parser for whole compilation units (aka 'Stored_Definition')
    @raise SyntaxError on syntax-error
*)

