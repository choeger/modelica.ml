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

(** Modelica pretty-printers. Implementation is based on [Format] pretty-printing, but the 
    [Format]-based API is not (yet) exposed to keep the documentation workload small. Patches welcome.

    All pretty printers return correct (i.e. parseable) Modelica Syntax.
*)

val eq2str : ?max:int -> Syntax.equation -> string
(** Equation pretty printer. 
    @param max The maximum number of boxes opened (as defined by [Format.set_max_boxes])
 *)
                                              
val import2str : ?max:int -> Syntax.import -> string
(** [import]-clause pretty printer. 
    @param max The maximum number of boxes opened (as defined by [Format.set_max_boxes])
 *)
                                                
val extend2str : ?max:int -> Syntax.extend -> string
(** [extends]-clause pretty printer. 
    @param max The maximum number of boxes opened (as defined by [Format.set_max_boxes])
 *)
                                                
val texpr2str : ?max:int -> Syntax.texp -> string
(** Equation pretty printer. 
    @param max The maximum number of boxes opened (as defined by [Format.set_max_boxes])
 *)
                                             
val td2str : ?max:int -> Syntax.typedef -> string
(** Type-Definition pretty printer
    @param max The maximum number of boxes opened (as defined by [Format.set_max_boxes])
 *)

val defs2str : ?max:int -> Syntax.definition list -> string
(** Definition pretty printer. 
    Since modelica.ml factors definitions (i.e. [parameter Real x,y;] becomes [parameter Real x; parameter Real y]),
    it works on a list instead of singletons.
    @param max The maximum number of boxes opened (as defined by [Format.set_max_boxes])
 *)
                                                       
val stmt2str : ?max:int -> Syntax.statement -> string
(** Statement pretty printer. 
    @param max The maximum number of boxes opened (as defined by [Format.set_max_boxes])
 *)
                                                 
val texpr2str : ?max:int -> Syntax.texp -> string
(** Type-expresssion pretty printer
    @param max The maximum number of boxes opened (as defined by [Format.set_max_boxes])
 *)

val unit2str : ?max:int -> Syntax.unit_ -> string
(** Compilation unit (aka 'Stored_Definition') pretty printer
    @param max The maximum number of boxes opened (as defined by [Format.set_max_boxes])
 *)
                                                                                          
val expr2str : ?max:int -> Syntax.exp -> string
(** Expresssion pretty printer
    @param max The maximum number of boxes opened (as defined by [Format.set_max_boxes])
 *)

                                             
