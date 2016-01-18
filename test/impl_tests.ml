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

open OUnit2
open Batteries
open Modlib
open Utils
open Syntax
open Syntax_fragments
open Normalized
open NormImpl
open NormLib
open TestUtils
open ClassValueFragments
open P

module S = Syntax_fragments

let public = true
let protected = false

let test_cases = [
  test_env "Empty class" "class A end A" [`ClassMember "A"] NormImpl.empty_env ;

  test_env "Constant" "class A constant Real x = 42. ; end A" [`ClassMember "A"]
    {public_env=StrMap.of_list [("x", EnvField (const Real))]; protected_env=StrMap.empty} ;

  test_env "Protected Constant" "class A protected constant Real x = 42. ; end A" [`ClassMember "A"]
    {public_env=StrMap.empty; protected_env=StrMap.of_list [("x", EnvField (const Real))]} ;

  test_env "Type declaration" "class A type X = constant Real; end A" [`ClassMember "A"]
    {public_env=StrMap.of_list [("X", EnvClass (const (type_ Real)))]; protected_env=StrMap.empty} ;

  test_env "Inherited type declaration"
    "class A class B type X = constant Real; end B; class C extends B; end C; end A"
    [`ClassMember "A"; `ClassMember "C"]
    {public_env=StrMap.of_list [("X", EnvClass (const (type_ Real)))]; protected_env=StrMap.empty} ;

  test_ctxt "Simple context"
    "class A class B end B; end A"
    [`ClassMember "A"; `ClassMember "B"] ;

  test_ctxt "Simple context"
    "class A class B class C end C; end B; end A"
    [`ClassMember "A"; `ClassMember "B"; `ClassMember "C"] ;

  (
  let b = Class {empty_object_struct with source_path = Inter.Path.of_list [`ClassMember "A"; `ClassMember "B"] } in 
  test_lex_env "Simple lexical environment"
    "class A constant Real x = 42.; class B end B; end A"
    [`ClassMember "A"; `ClassMember "B"] 
    [ empty_env; {empty_env with public_env = StrMap.of_list ["B", EnvClass b; "x", EnvField (const Real)]} ] ) ; 

  test_norm "Normalize Simple Binding"
    "class A constant Real x = 42.; end A"
    [`ClassMember "A"] (Has.field public "x" (Is.bound_to (Real 42.))) ;

  test_norm "Normalize Simple Protected Binding"
    "class A protected constant Real x = 42.; end A"
    [`ClassMember "A"] (Has.field protected "x" (Is.bound_to (Real 42.))) ;

  test_norm "Normalize Binding to Builtin Attributes"
    "class A constant Real x = y.start; Real y; end A"
    [`ClassMember "A"] (Has.field public "x" (Is.bound_to (cre (knownref [cclass "A"; cfld "y"; cattr "start"])))) ;  

  test_norm "Normalize Builtin 'size'"
    "class A constant Integer x = size(y); Real y; end A"
    [`ClassMember "A"] (Has.field public "x" (Is.bound_to (app {fun_= knownref [cbuiltinfun "size"] ;
                                                            args=[cre (knownref [cclass "A"; cfld "y"])];
                                                            named_args=[]}))) ;

  test_norm "Normalize Builtin 'stateSelect'"
    "class A Real y(stateSelect=StateSelect.never); end A"
    [`ClassMember "A"] (Has.field public "y" (Has.modification "stateSelect" (
        Has.modification_kind CK_BuiltinAttr &&&
        Is.modified_to (cre (knownref [cbuiltinclass "StateSelect" ; cattr "never"] ))))) ;

  test_norm "Normalize Builtin 'stateSelect' in an array"
    "class A Real[3] y(stateSelect=StateSelect.never); end A"
    [`ClassMember "A"] (Has.field public "y" (Has.modification "stateSelect" (
        Has.modification_kind CK_BuiltinAttr &&&
        Is.modified_to (cre (knownref [cbuiltinclass "StateSelect" ; cattr "never"] ))))) ;

  test_norm "Normalize Builtin 'stateSelect' in an extended array"
    "class A T y(stateSelect=StateSelect.never); type T extends Real[3]; end T; end A"
    [`ClassMember "A"] (Has.field public "y" (Has.modification "stateSelect" (
        Has.modification_kind CK_BuiltinAttr &&&
        Is.modified_to (cre (knownref [cbuiltinclass "StateSelect" ; cattr "never"] ))))) ;
  
  test_norm "Normalize Builtin 'String'"
    "class A constant Integer x = String(1); end A"
    [`ClassMember "A"] (Has.field public "x" (Is.bound_to (app {fun_= knownref [cbuiltinclass "String"] ;
                                                                args=[S.int 1];
                                                                named_args=[]}))) ;
  
  test_norm "Normalize Simple Modification"
    "class A constant Real x(start = 42.); end A"
    [`ClassMember "A"] (Has.field public "x" (Has.modification "start" (Is.modified_to (Real 42.)))) ;  
  
  test_norm "Normalize Simple Protected Modification"
    "class A protected constant Real x(start = 42.); end A"
    [`ClassMember "A"] (Has.field protected "x" (Has.modification "start" (
        (Is.modified_to (Real 42.)) &&& (Has.modification_kind CK_BuiltinAttr)
      )));

  test_norm "Normalize Class Modification"
    "class A class B constant Real x = 42.; end B; class C = B(x = 21.); end A"
    [`ClassMember "A"] (Has.class_member public "C" (Has.class_modification "x" (
        (Has.modification_kind CK_Constant)
        &&& 
        (Is.modified_to (Real 21.)) ))) ;

  test_norm "Normalize Nested Class Modification"
    "class A class B constant Real x = 42.; end B; class C class B = .A.B(x = 21.); end C; class D = C(B(x=42.)); end A"
    [`ClassMember "A"] (Has.class_member public "D" (Has.class_modification "B" (
        (Has.modification_kind CK_Class)
        &&&
        (Is.nested (Has.element "x" (            
             (Has.modification_kind CK_Constant) &&& (Is.modified_to (Real 42.))))
          ) ))) ;
  
  test_norm "Normalize Nested Class Modification to a field"
    "class A class B constant Real x = 42.; end B; class C class B = .A.B(x = 21.); end C; class D C c(B(x=42.)); end D; end A"
    [`ClassMember "A"; `ClassMember "D"] (Has.field public "c" (Has.modification "B" (
        (Has.modification_kind CK_Class)
        &&&
        (Is.nested (Has.element "x" (            
             (Has.modification_kind CK_Constant) &&& (Is.modified_to (Real 42.))))
        ) ))) ;
  
  test_norm "Self Name Resolution Inside Binding"
    "class A class B constant Real x = x; end B; protected constant Real x = 42.; end A"
    [`ClassMember "A"; `ClassMember "B"] (Has.field public "x" (Is.bound_to (ComponentReference (knownref [cclass "A"; cclass "B"; cconstfld "x"]))));

  test_norm "Name Resolution Inside Binding"
    "class A constant Real y = x; constant Real x = 42.; end A"
    [`ClassMember "A"] (Has.field public "y" (Is.bound_to (ComponentReference (knownref [cclass "A"; cconstfld "x"])))) ;

  test_norm "Protected Name Resolution Inside Binding"
    "class A constant Real y = x; protected constant Real x = 42.; end A"
    [`ClassMember "A"] (Has.field public "y" (Is.bound_to (ComponentReference (knownref [cclass "A"; cconstfld "x"])))) ;

  test_norm "Inherited Name Resolution Inside Binding"
    "class A class B constant Real x = 42.; end B; class C extends B; protected constant Real y = x; end C; end A"
    [`ClassMember "A"; `ClassMember "C"]
    (Has.field protected "y"
       (Is.bound_to (ComponentReference (knownref [cclass "A"; cclass "C"; cconstfld "x"]))))  ;

  test_norm
    "Lookup a modified constant in a simple Modelica class using extensions" 
    "package A model C extends B(x = 21.); end C; model B constant Real x = 42.; end B; end A" 
    [`ClassMember "A"; `ClassMember "C"] (Has.field public "x"  
    (Is.bound_to (Real 21.))) ;   

  test_norm
    "Lookup a modified constant in a component using extensions" 
    "package A C c(x = 21.); model C extends B; end C; model B constant Real x = 42.; end B; end A" 
    [`ClassMember "A"] (Has.field public "c" **> Has.modification "x" **> (Has.modification_kind CK_Constant &&& Is.modified_to (Real 21.)));

  test_norm
    "Lookup imported names"
    "package A package B constant Real x = 42.; end B; package C import A.B.x; constant Real y = x; end C; end A"
    [cm "A"; cm "C"] (Has.field public "y" **> Is.bound_to (ComponentReference (knownref [cclass "A"; cclass "B"; cconstfld "x"])));
  
  (
  let expected_ref = knownref [cclass "A"; cfld "x"] in 
  test_norm
    "Lookup an unknown in an equation"
    "model A Real x; equation x = 0.0; end A"
    [`ClassMember "A"] (Has.behavior **> Has.equations **> The.first **> Is.equation {comment = no_comment; commented = SimpleEquation {left=ComponentReference expected_ref; right=Real 0.0}}) );

  (* Attempt to test a typical medium library pattern *)
  test_norm
    "Forwarding a Redeclaration into a Component (Media Library Pattern)"
    "package MiniMedium
       package DefaultMedium end DefaultMedium ;
       package NonDefaultMedium constant Real foo = 42.; end NonDefaultMedium;
       class Interface replaceable package Medium = DefaultMedium; end Interface;
       
       class SomeComponent extends Interface; Medium medium; end SomeComponent;
       
       class SomeModel extends Interface(redeclare package Medium = NonDefaultMedium); 
             SomeComponent component(redeclare package Medium = Medium, medium(foo = 23.)); 
       end SomeModel;
     end MiniMedium"
    [`ClassMember "MiniMedium"; `ClassMember "SomeModel"]
    (Has.field public "component" **> Has.modification "medium" **> Is.nested **> Has.element "foo"
       (Has.modification_kind CK_Constant     &&&
        (Is.modified_to (Real 21.)))) ;

]

let suite = "Implementation Normalization" >::: test_cases

