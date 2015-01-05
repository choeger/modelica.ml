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

module Enum = BatEnum
open Format
open Utils
open Syntax

let rec pp_list ?(sep="") pp_element fmt = function
  | [h] -> Format.fprintf fmt "%a" pp_element h
  | h::t ->
    Format.fprintf fmt "%a%s@,%a"
      pp_element h sep (pp_list ~sep pp_element) t
  | [] -> ()

let pp_option ?(default="") pp_element fmt = function
  | Some a -> Format.fprintf fmt "%a" pp_element a
  | None -> Format.fprintf fmt "%s" default
            
let rec pp_enum ?(sep="") pp_element fmt enum = match (Enum.get enum) with
  | Some h -> Format.fprintf fmt "%a" pp_element h ; 
	      begin match (Enum.peek enum) with
		    | None -> ()
		    | Some(h) -> Format.fprintf fmt "%s@,%a" sep (pp_enum ~sep pp_element) enum
	      end
  | None -> ()

let rec pp_elseif pp_expr pp_then kw fmt {guard; elsethen} =
  fprintf fmt "@[ else%s@ %a@ then@ %a@]" kw pp_expr guard pp_then elsethen

and pp_complete_conditional ?else_:(else_kw=" else") pp_expr kw pp_then fmt { condition; then_ ; else_if; else_ } =
    fprintf fmt "@[%s@ %a@ then@ %a%a%s@ %a@]" kw
            pp_expr condition
            pp_then then_
            (pp_list (pp_elseif pp_expr pp_then kw)) else_if
            else_kw
            pp_then else_

let rec pp_expr fmt = function
    Ide(x) -> fprintf fmt "@[%s@]" x
  | RootIde(x) -> fprintf fmt "@[.%s@]" x
  | If c -> pp_complete_conditional pp_expr "if" pp_expr fmt c
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
  | Empty -> fprintf fmt "@[()@]"
                     
and pp_named_arg fmt (name,expr) =
  fprintf fmt "@[%s = %a@]" name pp_expr expr

and pp_foridx fmt = function
    { variable ; range=Some(e) } -> fprintf fmt "@[%s in %a@]" variable pp_expr e
  | { variable ; range=None } -> fprintf fmt "@[%s@]" variable

let pp_conditional kw ?else_:(else_kw="else") pp_then fmt c=
  fprintf fmt "@[" ;
  pp_complete_conditional ~else_:else_kw pp_expr kw pp_then fmt c;
  fprintf fmt "end@ %s@]" kw 
                                         
let expr2str ?max:(n=8) e = 
  pp_set_max_boxes str_formatter n ;
  (pp_expr str_formatter e) ;
  flush_str_formatter ()

let pp_typedef fmt { commented = { td_name ; sort ; type_exp ; cns ; type_options } ; comment } = ()
                      
let pp_type_redeclaration fmt { redecl_each ; redecl_type } =
  if redecl_each then
    fprintf fmt "@[each@ %a@]" pp_typedef redecl_type
  else
    pp_typedef fmt redecl_type

let pp_component_redeclaration fmt { each ; def } = ()

let pp_component_modification fmt { commented = { mod_each ; mod_final ; mod_name ; mod_modification ; mod_rhs } ; comment } = ()
                                                      
let pp_modification fmt { types ; components ; modifications } =
  pp_list pp_type_redeclaration fmt types ;
  pp_list pp_component_redeclaration fmt components ;
  pp_list pp_component_modification fmt modifications

let pp_annotation fmt = function
    None -> ()
  | Some m -> fprintf fmt "@[annotation%a@]" pp_modification m
          
let pp_comment_string fmt = function
  | None -> ()
  | Some s -> fprintf fmt " %s" s 
          
let pp_comment fmt { annotated_elem ; annotation } = 
  pp_comment_string fmt annotated_elem ;
  pp_annotation fmt annotation 
              
let pp_for_loop pp fmt { idx ; body } =
  fprintf fmt "@[for@ %a@ loop@ %a@ end for@]" (pp_list ~sep:", " pp_foridx) idx pp body
          
let rec pp_statement_desc fmt = function
    Assignment { target; source} -> fprintf fmt "@[%a@ :=@ %a@]" pp_expr target pp_expr source 
  | Call { procedure ; pargs ; pnamed_args } -> fprintf fmt "@[%a@]" pp_expr (App {fun_=procedure ; args=pargs; named_args=pnamed_args })
                                                      
  | IfStmt c -> pp_conditional "if" pp_statements fmt c 
  | WhenStmt c -> pp_conditional "when" ~else_:"" pp_statements fmt c 
                  
  | Break -> fprintf fmt "@[break@]"
  | Return -> fprintf fmt "@[return@]"
  | ForStmt loop -> pp_for_loop pp_statements fmt loop
  | WhileStmt { while_ ; do_ } -> fprintf fmt "@[while@ %a@ loop@ %a@ end@ while@]" pp_expr while_ pp_statements do_

and pp_statements fmt stmts = (pp_list pp_statement) fmt stmts
       
and pp_statement fmt { commented ; comment } =
  fprintf fmt "@[%a%a;@]" pp_statement_desc commented pp_comment comment 

let stmt2str ?max:(n=8) s = 
  pp_set_max_boxes str_formatter n ;
  (pp_statement str_formatter s) ;
  flush_str_formatter ()


let rec pp_equation_desc fmt = function
    SimpleEquation { eq_lhs ; eq_rhs } -> fprintf fmt "@[%a@ =@ %a@]"
                                                  pp_expr eq_lhs pp_expr eq_rhs
  | ForEquation loop -> pp_for_loop pp_equations fmt loop
  | IfEquation c -> pp_conditional "if" pp_equations fmt c 
  | WhenEquation c -> pp_conditional "when" ~else_:"" pp_equations fmt c
  | ExpEquation e -> pp_expr fmt e

and pp_equation fmt { commented ; comment } =
  fprintf fmt "@[%a%a;@]" pp_equation_desc commented pp_comment comment 

and pp_equations fmt eqs = (pp_list pp_equation) fmt eqs

let eq2str ?max:(n=8) eq = 
  pp_set_max_boxes str_formatter n ;
  (pp_equation str_formatter eq) ;
  flush_str_formatter ()

let pp_variability fmt = function
  | Constant -> fprintf fmt "constant"
  | Parameter -> fprintf fmt "parameter"
  | Discrete -> fprintf fmt "discrete"

let pp_causality fmt = function
  | Input -> fprintf fmt "input"
  | Output -> fprintf fmt "output"

let pp_connectivity fmt = function
  | Flow -> fprintf fmt "flow"
  | Stream -> fprintf fmt "stream"
                      
let rec pp_texpr fmt = function
  | TIde x -> fprintf fmt "@[%s@]" x
  | TProj { class_type; type_element } -> fprintf fmt "@[%a.%s@]" pp_texpr class_type type_element
  | TRootide x -> fprintf fmt "@[.%s@]" x
  | TVar { flag ; flagged } -> fprintf fmt "@[%a@ %a@]" pp_variability flag pp_texpr flagged
  | TCon { flag ; flagged } -> fprintf fmt "@[%a@ %a@]" pp_connectivity flag pp_texpr flagged
  | TCau { flag ; flagged } -> fprintf fmt "@[%a@ %a@]" pp_causality flag pp_texpr flagged
  | TArray { base_type ; dims } -> fprintf fmt "@[%a[%a]@]" pp_texpr base_type (pp_list ~sep:", " pp_expr) dims
  | TMod { mod_type ; modification } -> fprintf fmt  "@[%a(%a)@]" pp_texpr mod_type pp_modification modification

                                           
let texpr2str ?max:(n=8) te = 
  pp_set_max_boxes str_formatter n ;
  (pp_texpr str_formatter te) ;
  flush_str_formatter ()

let pp_import_desc fmt = function
    Unnamed name -> fprintf fmt "@[import@ %a@]" (pp_list ~sep:"." pp_print_string) name 
  | NamedImport {from; selected} -> fprintf fmt "@[import@ %a@ =@ %s@]" (pp_list ~sep:"." pp_print_string) from selected
  | UnqualifiedImport name -> fprintf fmt "@[import@ %a.*@]" (pp_list ~sep:"." pp_print_string) name 
    
let pp_import fmt {commented;comment} =
  fprintf fmt "@[%a%a@]" pp_import_desc commented pp_comment comment
                            
let import2str ?max:(n=8) import = 
  pp_set_max_boxes str_formatter n ;
  (pp_import str_formatter import) ;
  flush_str_formatter ()

let pp_extend fmt = function
  | { ext_type ; ext_visibility ; ext_annotation } ->
     fprintf fmt "@[%s@ extends@ %a%a@]"
             (match ext_visibility with Public -> "public" | Protected -> "protected")
             pp_texpr ext_type pp_annotation ext_annotation

let extend2str ?max:(n=8) extends = 
  pp_set_max_boxes str_formatter n ;
  (pp_extend str_formatter extends) ;
  flush_str_formatter ()

let pp_def_if fmt cond =
  fprintf fmt "@[@ if@ %a@]" pp_expr cond

let pp_def_rhs fmt rhs =
  fprintf fmt "@[@ =@ %a@]" pp_expr rhs

let pp_visibility fmt = function
  | Public -> pp_print_string fmt "public"
  | Protected -> pp_print_string fmt "protected"

let pp_scope fmt = function
  | Inner -> pp_print_string fmt "inner"
  | Outer -> pp_print_string fmt "inner"
  | InnerOuter ->  pp_print_string fmt "inner outer"
  | Local -> ()

let pp_def_options fmt { final ; scope ; visibility ; replaceable } =
  fprintf fmt "@[%a%s%s%a@]" pp_visibility visibility
          (if final then "final" else "")
          (if replaceable then "replaceable" else "")
          pp_scope scope

let pp_constraint fmt { commented ; comment } =
  fprintf fmt "@[constrainedby %a%a@]"  pp_texpr commented  pp_comment comment                  
          
let pp_def_desc fmt { def_name; def_type; def_constraint;
                      def_rhs; def_if; def_options} =
  fprintf fmt "@[%a@ %a@ %a%a%a%a@]" pp_def_options def_options
          pp_texpr def_type
          pp_print_string def_name  
          (pp_option pp_def_rhs) def_rhs
          (pp_option pp_def_if) def_if
          (pp_option pp_constraint) def_constraint
          
let pp_definition fmt { commented ; comment } =
  fprintf fmt "@[%a%a@]" pp_def_desc commented pp_comment comment

let def_sep fmt () =
  fprintf fmt ";@."
          
let defs2str ?max:(n=8) defs = 
  pp_set_max_boxes str_formatter n ;
  pp_print_list ~pp_sep:def_sep pp_definition str_formatter defs ;
  flush_str_formatter ()
                      
