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


(**
 Modelica 3.x normalized types
 *)

open Utils
open Generic_syntax.Flags
       
type type_ = Int | Real | String | Bool | Unit
             | Array of array_struct
             | ExternalObject of type_ object_struct
             | Enumeration of StrSet.t
             | Record of type_ object_struct
             | Package of type_ object_struct
             | Model of component_type object_struct
             | Recursive of recursive_struct
             | Function of function_type
             | Variable of string

 and recursive_struct = { recursive_name : string ; recursive_rhs : type_ }

 and array_struct = { element : type_ ; dimensions : int }

 and 'a object_struct = { dynamic_fields : 'a StrMap.t ; static_fields : type_ StrMap.t }                         
                             
 and function_type = { inputs : (string * type_) StrMap.t ; outputs : type_ list }
                                              
 and component_type = { cmp_variability : variability ;
                        cmp_causality : causality ;
                        cmp_connectivity : connectivity ;
                        cmp_type : type_ }

                        
 and type_annotation = SimpleType of type_ | ComponentType of component_type | UnknownType
                        
module TypeAttribute = struct type t = type_annotation end
                        
module AnnotatedSyntax = Generic_syntax.Make(TypeAttribute) 

module DS = Syntax
module AS = AnnotatedSyntax
              
type env = {root : type_annotation StrMap.t ; current : type_annotation StrMap.t }

type error = UnknownIdentifier of string
           | UnknownGlobal of string

open Batteries
open Result

let rec result_mmap f = function
    [] -> Result.Monad.return []
  | x::xs -> Result.Monad.do_ ; x' <-- f x ; xs' <-- result_mmap f xs ; return (x'::xs')

let result_mmap_opt f = function
    None -> Result.Monad.return None
  | Some x -> Result.Monad.do_ ; x' <-- f x; return (Some x')
                                                                               
let rec tc env {DS.term = t} = type_check env t
                           
and type_check {root;current} = function 
    DS.Ide x when StrMap.mem x current -> let attr = StrMap.find x current in Ok {AS.term = AS.Ide x ; attr}
  | DS.RootIde x when StrMap.mem x root -> let attr = StrMap.find x root in Ok {AS.term = AS.Ide x ; attr}
  | DS.Ide x -> Bad (UnknownIdentifier x)
  | DS.RootIde x -> Bad (UnknownGlobal x)

  | Pow {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}
                                
  | DPow {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | Mul {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | DMul {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | Div {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | DDiv {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | Plus {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | DPlus {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | Minus {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | DMinus {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | And {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | Or {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | Gt {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | Lt {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | Leq {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | Geq {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | Neq {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | Eq {left; right} -> Result.Monad.do_ ;
                         left <-- tc {root;current} left ;
                         right <-- tc {root;current} right ;
                         return {AS.term = AS.Pow {left; right}; attr = UnknownType}

  | UMinus e -> Result.Monad.do_ ;
                e <-- tc {root;current} e ;
                return {AS.term = AS.UMinus e; attr = UnknownType}

  | UPlus e -> Result.Monad.do_ ;
               e <-- tc {root;current} e ;
               return {AS.term = AS.UMinus e; attr = UnknownType}

  | UDMinus e -> Result.Monad.do_ ;
               e <-- tc {root;current} e ;
               return {AS.term = AS.UMinus e; attr = UnknownType}

  | UDPlus e -> Result.Monad.do_ ;
               e <-- tc {root;current} e ;
               return {AS.term = AS.UMinus e; attr = UnknownType}

  | Not e -> Result.Monad.do_ ;
               e <-- tc {root;current} e ;
               return {AS.term = AS.UMinus e; attr = UnknownType}
  
  | If { condition; then_; else_if; else_} ->
     let tc_else_if env {DS.guard;elsethen} = Result.Monad.do_ ; guard <-- tc env guard ; elsethen <-- tc env elsethen ; return {AS.guard = guard; elsethen} in
                                                                                                                             
     Result.Monad.do_ ;
     condition <-- tc {root; current} condition ;
     then_ <-- tc {root; current} then_ ;
     else_if <-- result_mmap (tc_else_if {root; current}) else_if ;
     else_ <-- tc {root; current} else_ ;
     return { AS.term = AS.If {condition; then_; else_if; else_}; attr=UnknownType}
                                                                                              
  | ArrayAccess {lhs; indices} ->
     Result.Monad.do_ ;
     lhs <-- tc {root; current} lhs ;
     indices <-- result_mmap (tc {root;current}) indices ;
     return {AS.term = ArrayAccess {lhs; indices}; attr = UnknownType }
            
  | Range {start; end_; step} ->
     Result.Monad.do_ ;
     start <-- tc {root; current} start ;
     end_ <-- tc {root; current} end_ ;
     step <-- result_mmap_opt (tc {root;current}) step ;
     return {AS.term = Range {start; end_; step} ; attr=UnknownType}
            
  | Proj {field; object_} ->
     Result.Monad.do_ ;
     object_ <-- tc {root; current} object_ ;
     return {AS.term=Proj {field; object_}; attr = UnknownType }
            
  | App {fun_; args ; named_args} ->
     let tc_named_arg env {DS.argument; argument_name} = Result.Monad.do_ ; argument <-- tc env argument ; return {AS.argument_name = argument_name; argument} in
     Result.Monad.do_ ;
     fun_ <-- tc {root; current} fun_ ;
     args <-- result_mmap (tc {root;current}) args ;
     named_args <-- result_mmap (tc_named_arg {root;current}) named_args ;
     return {AS.term = App {fun_; args ; named_args}; attr = UnknownType }

  | Bool x -> Ok {AS.term = Bool x; attr = UnknownType}
  | Int x -> Ok {AS.term = Int x; attr = UnknownType}
  | Real x -> Ok {AS.term = Real x; attr = UnknownType}
  | String x -> Ok {AS.term = String x; attr = UnknownType}
  | End -> Ok {AS.term = End; attr = UnknownType}
  | Colon -> Ok {AS.term = Colon ; attr = UnknownType}
  | Der -> Ok {AS.term = Der ; attr = UnknownType}
  | Initial -> Ok {AS.term = Initial ; attr = UnknownType}
  | Assert -> Ok {AS.term = Assert ; attr = UnknownType}
                      
  | Compr {exp; idxs} ->
     let tc_idx env { DS.variable; range } = Result.Monad.do_ ; range <-- result_mmap_opt (tc env) range ; return { AS.variable = variable ; range } in
     Result.Monad.do_ ;
     exp <-- tc {root; current} exp ;
     idxs <-- result_mmap (tc_idx {root; current}) idxs ;
     return {AS.term = Compr {exp; idxs}; attr = UnknownType }

            
  | Array es -> Result.Monad.do_ ; es' <-- result_mmap (tc {root;current}) es ; return {AS.term=Array es'; attr = UnknownType}
  | MArray ess -> Result.Monad.do_ ; ess' <-- result_mmap (result_mmap (tc {root;current})) ess ; return {AS.term=MArray ess'; attr = UnknownType}
  | ExplicitClosure e ->  Result.Monad.do_ ;
                          e <-- tc {root;current} e ;
                          return {AS.term = AS.UMinus e; attr = UnknownType}

  | OutputExpression eos -> Result.Monad.do_ ; eos' <-- result_mmap (result_mmap_opt (tc {root;current})) eos ; return {AS.term=OutputExpression eos'; attr = UnknownType}
