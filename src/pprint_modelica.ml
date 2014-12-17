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
open Utils
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
  | RootIde(x) -> fprintf fmt "[@.%s@]" x
  | If {condition; then_; else_if; else_} -> fprintf fmt "@[if@ %a@ then@ %a@ else@ %a @]" pp_expr condition pp_expr then_ pp_expr else_
  | Int(i) -> fprintf fmt "@[%d@]" i
  | Real(f) -> fprintf fmt "@[%f@]" f
  | Bool(b) -> fprintf fmt "@[%b@]" b
  | String(s) -> fprintf fmt "@[\"%s\"@]" (String.escaped s)
  | Proj {field; object_} -> fprintf fmt "@[%a.%s@]" pp_expr object_ field
  | Der -> fprintf fmt "@[der@]"
  | End -> fprintf fmt "@[end@]"
  | Colon -> fprintf fmt "@[:@]"
  | Initial -> fprintf fmt "@[initial@]"

  | Pow { left; right } -> fprintf fmt "@[(%a)^(%a)@]" pp_expr left pp_expr right                  
  | DPow { left; right } -> fprintf fmt "@[(%a).^(%a)@]" pp_expr left pp_expr right                  
  | Plus { left; right } -> fprintf fmt "@[(%a)+(%a)@]" pp_expr left pp_expr right                  
  | DPlus { left; right } -> fprintf fmt "@[(%a).+(%a)@]" pp_expr left pp_expr right                  
  | Minus { left; right } -> fprintf fmt "@[(%a)-(%a)@]" pp_expr left pp_expr right                  
  | DMinus { left; right } -> fprintf fmt "@[(%a).-(%a)@]" pp_expr left pp_expr right                  
  | Mul { left; right } -> fprintf fmt "@[(%a)*(%a)@]" pp_expr left pp_expr right                  
  | DMul { left; right } -> fprintf fmt "@[(%a).*(%a)@]" pp_expr left pp_expr right                  
  | Div { left; right } -> fprintf fmt "@[(%a)/(%a)@]" pp_expr left pp_expr right                  
  | DDiv { left; right } -> fprintf fmt "@[(%a)./(%a)@]" pp_expr left pp_expr right                  

  | Leq { left; right } -> fprintf fmt "@[(%a)<=(%a)@]" pp_expr left pp_expr right                  
  | Lt { left; right } -> fprintf fmt "@[(%a)<(%a)@]" pp_expr left pp_expr right                  
  | Geq { left; right } -> fprintf fmt "@[(%a)>=(%a)@]" pp_expr left pp_expr right                  
  | Gt { left; right } -> fprintf fmt "@[(%a)>(%a)@]" pp_expr left pp_expr right                  
  | Eq { left; right } -> fprintf fmt "@[(%a)==(%a)@]" pp_expr left pp_expr right                  
  | Neq { left; right } -> fprintf fmt "@[(%a)<>(%a)@]" pp_expr left pp_expr right                  

  | And { left; right } -> fprintf fmt "@[(%a) and (%a)@]" pp_expr left pp_expr right                  
  | Or { left; right } -> fprintf fmt "@[(%a) or (%a)@]" pp_expr left pp_expr right                  

  | UPlus e -> fprintf fmt "@[+(%a)@]" pp_expr e
  | UDPlus e -> fprintf fmt "@[.+(%a)@]" pp_expr e
  | UMinus e -> fprintf fmt "@[-(%a)@]" pp_expr e
  | UDMinus e -> fprintf fmt "@[.+(%a)@]" pp_expr e
  | Not e -> fprintf fmt "@[not (%a)@]" pp_expr e

  | App { fun_ ; args=[] ; named_args } -> fprintf fmt "@[%a(%a)@]" pp_expr fun_ (pp_enum ~sep:", " pp_named_arg) (StrMap.enum named_args)
  | App { fun_ ; args ; named_args } when named_args = StrMap.empty -> fprintf fmt "@[%a(%a)@]" pp_expr fun_ (pp_list ~sep:", " pp_expr) args
  | App { fun_ ; args; named_args } -> fprintf fmt "@[%a(%a, %a)@]" pp_expr fun_ (pp_list ~sep:", " pp_expr) args (pp_enum ~sep:", " pp_named_arg) (StrMap.enum named_args)

  | Range { start; end_; step = None } -> fprintf fmt "@[(%a):(%a)@]" pp_expr start pp_expr end_
  | Range { start; end_; step = Some(s)  } -> fprintf fmt "@[(%a):(%a):(%a)@]" pp_expr start pp_expr s pp_expr end_
  | Compr { exp ; idxs } -> fprintf fmt "@[(%a) for %a@]" pp_expr exp (pp_list ~sep:", " pp_foridx) idxs
  | Array es -> fprintf fmt "@[{%a}@]" (pp_list ~sep:", " pp_expr) es
  | MArray els -> fprintf fmt "@[[%a]@]" (pp_list ~sep:"; " (pp_list ~sep:", " pp_expr)) els
  | ArrayAccess { lhs ; indices } -> fprintf fmt "@[%a[%a]@]" pp_expr lhs (pp_list ~sep:", " pp_expr) indices 
  | ExplicitClosure e -> fprintf fmt "@[function %a@]" pp_expr e
  | Tuple es -> fprintf fmt "@[(%a)@]" (pp_list ~sep:", " pp_expr) es
  | Empty -> ()

and pp_named_arg fmt (name,expr) =
  fprintf fmt "@[%s = %a@]" name pp_expr expr

and pp_foridx fmt = function
    { variable ; range=Some(e) } -> fprintf fmt "@[%s in %a@]" variable pp_expr e
  | { variable ; range=None } -> fprintf fmt "@[%s@]" variable
                                         
let expr2str ?max:(n=8) e = 
  pp_set_max_boxes str_formatter n ;
  (pp_expr str_formatter e) ;
  flush_str_formatter ()
