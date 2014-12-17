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

open Batteries
open Format
open Syntax

let rec pp_list ?(sep="") pp_element fmt = function
  | [h] -> Format.fprintf fmt "%a" pp_element h
  | h::t ->
    Format.fprintf fmt "%a%s@,%a"
      pp_element h sep (pp_list ~sep pp_element) t
  | [] -> ()

let rec pp_enum ?(sep="") pp_element fmt enum = match (Enum.get enum) with
  | Some h -> Format.fprintf fmt "%a" pp_element h ; 
	      begin match (Enum.peek enum) with
		    | None -> ()
		    | Some(h) -> Format.fprintf fmt "%s@,%a" sep (pp_enum ~sep pp_element) enum
	      end
  | None -> ()

and pp_expr fmt = function
    Ide(x) -> fprintf fmt "@[%s@]" x
  | If {condition; then_; else_if; else_} -> fprintf fmt "@[if@ %a@ then@ %a@ else@ %a @]" pp_expr condition pp_expr then_ pp_expr else_
  | Int(i) -> fprintf fmt "@[%d@]" i
  | Real(f) -> fprintf fmt "@[%f@]" f
  | Bool(b) -> fprintf fmt "@[%b@]" b
  | String(s) -> fprintf fmt "@[\"%s\"@]" (String.escaped s)
  | Proj {field; object_} -> fprintf fmt "@[%a.%s@]" pp_expr object_ field
  | Der -> fprintf fmt "@[der@]"
  | End -> fprintf fmt "@[end@]"
  | Initial -> fprintf fmt "@[initial@]"
                  

                                                     
let expr2str ?max:(n=8) e = 
  pp_set_max_boxes str_formatter n ;
  (pp_expr str_formatter e) ;
  flush_str_formatter ()
