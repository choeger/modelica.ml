
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

(** Useful fragments of Modelica syntax *)

open Batteries
open Syntax
open Utils

let nl = Location.mknoloc

exception EmptyName

let rec name_ components = function
  | [] -> {components = List.rev components; root=false}
  | txt::r -> name_ ({ident = {txt; loc = Location.none}; subscripts=[]}::components) r

let unknownref = function
  | [] -> raise EmptyName
  | n -> UnknownRef (name_ [] n)

let name xs = let ur = unknownref xs in ComponentReference ur

let int x =  (Int x)
let real x =  (Real x)
let ide x = name [x]
let bool x =  (Bool x)
let string x =  (String x)
let colon =  Colon
let end_ =  End
let app x =  (App x)
let pow x =  (Pow x)
let dpow x =  (DPow x)
let mul x =  (Mul x)
let dmul x =  (DMul x)
let div x =  (Div x)
let ddiv x =  (DDiv x)
let plus x =  (Plus x)
let dplus x =  (DPlus x)
let minus x =  (Minus x)
let dminus x =  (DMinus x)
let uminus x =  (UMinus x)
let uplus x =  (UPlus x)
let udminus x =  (UDMinus x)
let udplus x =  (UDPlus x)
let gt x =  (Gt x)
let lt x =  (Lt x)
let leq x =  (Leq x)
let geq x =  (Geq x)
let neq x =  (Neq x)
let eq_ x =  (Eq x)
let and_ x =  (And x)
let or_ x =  (Or x)
let not_ x =  (Not x)
let if_ x =  (If x)
let range x =  (Range x)
let compr x =  (Compr x)
let array x =  (Array x)
let marray x =  (MArray x)
let explicitclosure x =  (ExplicitClosure x)
let outputexpression x =  (OutputExpression x)

let cr components = UnknownRef {root=false; components}
let cre cr =  (ComponentReference cr)

let der =  (ComponentReference Der)
let initial =  (ComponentReference Initial)
let assert_ =  (ComponentReference Assert)                   

let any x = {ident = nl x;subscripts=[]}                             

let empty_app f = { fun_ = f ; args = [] ; named_args = [] }

let named x argument = {argument_name = Location.mknoloc x ; argument }

let no_comment = { annotated_elem = None ; annotation = None }

let unannotated annotated_elem = { annotated_elem ; annotation = None }

let uncommented a = { commented = a ; comment = no_comment }

let no_modification = { types = [] ; components = [] ; modifications = [] }

let no_def_options = { final = false ; replaceable = false ; scope = Local }

let empty_def  = { def_name ="" ; def_type = TName []; def_options = no_def_options ; def_constraint = None ; def_rhs = None ; def_if = None }

let no_type_options = { partial = false ; encapsulated = false ;
                        type_final = false ; type_replaceable = false ;}

let empty_typedef = { td_name = Location.mknoloc "" ; type_exp = () ; type_options = no_type_options ; cns = None ; sort = Type}

let empty_behavior = { algorithms = [] ; initial_algorithms = [] ; equations = [] ; initial_equations = [] ; external_ = None }

let empty_elements = { defs = [] ; extensions = [] ; redeclared_defs = [] ;
                       typedefs = [] ; redeclared_types = [] }


let empty_composition = { imports = [] ; public = empty_elements ; protected = empty_elements ; cargo = empty_behavior  }

let type_name xs = TName (List.map Location.mknoloc xs)

let root_type xs = TRootName (List.map Location.mknoloc xs)

let known_component kind x = {kind;component={ident=nl x; subscripts=[]}}

let cclass = known_component CK_Class

let cvar = known_component CK_LocalVar

let cattr = known_component CK_BuiltinAttr

let cconstfld = known_component CK_Constant 

let time = known_component CK_Time "time"

let cfld = known_component CK_Continuous

let cbuiltinfun = known_component CK_BuiltinFunction

let cbuiltinclass = known_component CK_BuiltinClass
    
let knownref cks = KnownRef (DQ.of_list cks)

let rootref cks = RootRef (DQ.of_list cks)
