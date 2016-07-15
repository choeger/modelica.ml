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
(*  test_env "Empty class" "class A end A" [`ClassMember "A"] NormImpl.empty_env ;

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
*)
  
  test_norm "Normalize Simple Binding"
    "class A constant Real x = 42.; end A"
    [`ClassMember "A"] (Has.field public "x" (Is.bound_to (Real 42.))) ;


  (let app = {named_args=[]; fun_=UnknownRef {root=false;components=[{ident=nl "unquote"; subscripts=[]}]};
              args=[cre (knownref 0 [cconstfld ~known_type:FTReal "x"])]} in
  test_norm "Normalize Vendor specific Annotation"
    "class A constant Real x = 42.; annotation (__amsun(step = {unquote(x)})); end A"
    [`ClassMember "A"] (Has.annotation "__amsun" (Is.nested (Has.element "step" (Is.modified_to (Array [App app]))))) ) ;
  
  test_norm "Normalize Simple Protected Binding"
    "class A protected constant Real x = 42.; end A"
    [`ClassMember "A"] (Has.field protected "x" (Is.bound_to (Real 42.))) ;

  test_norm "Normalize Simple Outer-Scope Binding"
    "class A class B constant Real x = c; end B; constant Real c = 42.; end A"
    [cm "A"; cm "B"] (Has.field public "x" (Is.bound_to (cre (knownref 1 [cconstfld ~known_type:FTReal "c"])))) ;

  test_norm "Normalize Binding to Builtin Attributes"
    "class A constant Real x = y.start; Real y; end A"
    [`ClassMember "A"] (Has.field public "x" (Is.bound_to (cre (knownref 0 [cfld ~known_type:FTReal "y"; cattr ~known_type:FTReal "start"])))) ;  

  test_norm "Normalize Binding to Builtin Attributes, changing type"
    "class A constant Boolean x = y.fixed; Real y; end A"
    [`ClassMember "A"] (Has.field public "x" (Is.bound_to (cre (knownref 0 [cfld ~known_type:FTReal "y"; cattr ~known_type:FTBool "fixed"])))) ;  
  
  test_norm "Normalize Builtin 'size'"
    "class A constant Integer x = size(y); Real y; end A"
    [`ClassMember "A"] (Has.field public "x" (Is.bound_to (app (rootref [cbuiltinfun "size"]) 
                                                             ["", cre (knownref 0 [cfld ~known_type:FTReal "y"])])));
                                                            

  test_norm "Normalize Builtin 'stateSelect'"
    "class A Real y(stateSelect=StateSelect.never); end A"
    [`ClassMember "A"] (Has.field public "y" (Has.modification "stateSelect" (
        Has.modification_kind CK_BuiltinAttr &&&
        Is.modified_to (cre (rootref [cbuiltinclass "StateSelect" ; cattr "never"] ))))) ;

  test_norm "Normalize Builtin 'stateSelect' in an array"
    "class A Real[3] y(stateSelect=StateSelect.never); end A"
    [`ClassMember "A"] (Has.field public "y" (Has.modification "stateSelect" (
        Has.modification_kind CK_BuiltinAttr &&&
        Is.modified_to (cre (rootref [cbuiltinclass "StateSelect" ; cattr "never"] ))))) ;

  test_norm "Normalize Builtin 'stateSelect' in an extended array"
    "class A T y(stateSelect=StateSelect.never); type T extends Real[3]; end T; end A"
    [`ClassMember "A"] (Has.field public "y" (Has.modification "stateSelect" (
        Has.modification_kind CK_BuiltinAttr &&&
        Is.modified_to (cre (rootref [cbuiltinclass "StateSelect" ; cattr "never"] ))))) ;
  
  test_norm "Normalize Builtin 'String'"
    "class A constant Integer x = String(1); end A"
    [`ClassMember "A"] (Has.field public "x" (Is.bound_to (app (rootref [cbuiltinclass "String"]) 
                                                           ["", S.int 1])
                                             )) ;
  
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
    [`ClassMember "A"; `ClassMember "B"] (Has.field public "x" (Is.bound_to (ComponentReference (knownref 0 [cconstfld ~known_type:FTReal "x"]))));

  test_norm "Name Resolution Inside Binding"
    "class A constant Real y = x; constant Real x = 42.; end A"
    [`ClassMember "A"] (Has.field public "y" (Is.bound_to (ComponentReference (knownref 0 [cconstfld ~known_type:FTReal "x"])))) ;

  test_norm "Protected Name Resolution Inside Binding"
    "class A constant Real y = x; protected constant Real x = 42.; end A"
    [`ClassMember "A"] (Has.field public "y" (Is.bound_to (ComponentReference (knownref  0 [cconstfld ~known_type:FTReal "x"])))) ;

  test_norm "Inherited Name Resolution Inside Binding"
    "class A class E end E; class B constant Real x = 42.; end B; class C extends E; extends B; protected constant Real y = x; end C; end A"
    [`ClassMember "A"; `ClassMember "C"]
    (Has.field protected "y"
       (Is.bound_to (ComponentReference (knownref 0 [cconstfld ~known_type:FTReal "x"]))))  ;

  test_norm "Indirect Inherited Name Resolution"
    "class A class B Real a; end B; class C extends B; end C; class D C c; Real x = c.a; end D; end A"
    [`ClassMember "A"; `ClassMember "D"]
    (Has.field public "x" **> Is.bound_to (cre (knownref 0 [cfld "c"; cfld ~known_type:FTReal "a"]))) ;
    
  test_norm
    "Lookup a modified constant in a simple Modelica class using extensions" 
    "package A model C extends B(x = 21.); end C; model B constant Real x = 42.; end B; end A" 
    [`ClassMember "A"; `ClassMember "C"] (Has.super_class public 0 **>
                                          Has.super_class_modification "x" **> Is.modified_to (Real 21.)) ;   

  test_norm
    "Allow nested and default modifications at the same time" 
    "package A model B Real x(start = 0.0) = 42.; end B; end A" 
    [`ClassMember "A"; `ClassMember "B"] (Has.field public "x"
                                            (Has.modification "start" **> Is.modified_to (Real 0.0)
                                             &&&
                                             Is.bound_to (Real 42.))) ;   
  
  test_norm
    "Lookup a modified constant in a component using extensions" 
    "package A C c(x = 21.); model C extends B; end C; model B constant Real x = 42.; end B; end A" 
    [`ClassMember "A"] (Has.field public "c" **> Has.modification "x" **> (Has.modification_kind CK_Constant &&& Is.modified_to (Real 21.)));

  test_norm
    "Lookup imported names"
    "package A package B constant Real x = 42.; end B; package C import A.B.x; constant Real y = x; end C; end A"
    [cm "A"; cm "C"] (Has.field public "y" **> Is.bound_to (ComponentReference (rootref [cclass "A"; cclass "B"; cconstfld ~known_type:FTReal "x"])));


  (let known_type = Some (FTEnum (StrSet.of_list ["X";"Y"])) in
   let then_ = ComponentReference (rootref [cclass "A"; cclass "B"; cclass "S"; cattr ?known_type "X"]) in
   let yref = ComponentReference (rootref [cclass "A"; cclass "B"; cclass "S"; cattr ?known_type "Y"]) in
   let else_if = [{ guard = Bool true ; elsethen = yref }] in
   let else_ = then_ in   
   test_norm
     "Lookup an imported enumeration in a nested if-else-if-clause"
     "package A package B type S = enumeration(X,Y); end B; 
        package C 
          import A.B.S; 
          constant S s = if true then S.X elseif true then S.Y else S.X; 
        end C; 
     end A"
     [cm "A"; cm "C"] (Has.field public "s" **> Is.bound_to (If {condition=Bool true;then_;else_;else_if})));  


  (* Test for imported names in behavior section *)  
  (let known_type = Some (FTEnum (StrSet.of_list ["X";"Y"])) in
   let condition = Eq{
       left=ComponentReference (rootref [cclass "A"; cclass "B"; cclass "S"; cattr  ?known_type "X"]);
       right=ComponentReference (rootref [cclass "A"; cclass "B"; cclass "S"; cattr  ?known_type "Y"])};
   in 
   let eq = {left=ComponentReference (knownref 0 [cfld ~known_type:FTReal "x"]); right=ComponentReference (rootref [time])} in   
   let else_ = [uncommented (SimpleEquation {left=eq.right; right=eq.left})] in
   let then_ = [uncommented (SimpleEquation eq)] in
   let else_if = [] in
   test_norm
     "Lookup an imported enumeration in a nested if-equation"
     "package A package B type S = enumeration(X,Y); end B; 
        package C 
          import A.B.S; 
          Real x;
          equation          
          if S.X == S.Y then x = time; else time = x; end if; 
        end C; 
     end A"
     [cm "A"; cm "C"] (Has.behavior **> Has.equations **> The.first **> Is.equation (uncommented (IfEquation {condition;then_;else_;else_if}))));


  (* Test for iteration variables *)
  (
    let range = (Some (Range {start=Int 1; step = Some (Int 1); end_=Int 1})) in
    let assign = Assignment {target = Single (knownref 0 [cfld ~known_type:FTReal "x"]) ; source = ComponentReference (knownref 0 (*~typ:FTInteger*) [cvar "i"])} in
    let stmt = ForStmt {idx = [{variable=nl "i";range}]; body = [uncommented assign]} in
  test_norm
    "Lookup an iteration variable"
    "package A class B Real x; algorithm for i in 1:1:1 loop x := i; end for; end B; end A"
    [cm "A"; cm "B"] (Has.behavior **> Has.algorithms **> The.first **> The.first **> Is.statement (uncommented stmt))
  ) ;

  (
    let range = None in
    let assign = Assignment {target = Single (knownref 0 [cfld ~known_type:FTReal "x"]) ; source = ComponentReference (knownref 0 [cvar "i"])} in
    let stmt = ForStmt {idx = [{variable=nl "i";range}]; body = [uncommented assign]} in
  test_norm
    "Lookup an implicit iteration variable"
    "package A class B Real x; algorithm for i loop x := i; end for; end B; end A"
    [cm "A"; cm "B"] (Has.behavior **> Has.algorithms **> The.first **> The.first **> Is.statement (uncommented stmt))
  ) ;

  (
    let range = None in
    let assign = Assignment {target = Single (knownref 0 [cfld ~known_type:FTReal "x"]) ; source = ComponentReference (knownref 0 [cvar "j"])} in
    let stmt = ForStmt {idx = [{variable=nl "i";range}; {variable=nl "j";range}]; body = [uncommented assign]} in
  test_norm
    "Lookup multiple implicit iteration variables"
    "package A class B Real x; algorithm for i, j loop x := j; end for; end B; end A"
    [cm "A"; cm "B"] (Has.behavior **> Has.algorithms **> The.first **> The.first **> Is.statement (uncommented stmt))
  ) ;

  
  (* Test for iteration variables in equations *)
  (
    let range = (Some (Range {start=Int 1; step = Some (Int 1); end_=Int 1})) in
    let eq = SimpleEquation {left = ComponentReference (knownref 0 [cfld ~known_type:FTReal "x"]) ; right = ComponentReference (knownref 0 (*~typ:FTInteger*) [cvar "i"])} in
    let loop = ForEquation {idx = [{variable=nl "i";range}]; body = [uncommented eq]} in
  test_norm

    "Lookup an iteration variable in an equation"

    "package A class B Real x; equation for i in 1:1:1 loop x = i; end for; end B; end A"

    [cm "A"; cm "B"] (Has.behavior **> Has.equations **> The.first **> Is.equation (uncommented loop))
  ) ;

  (* Test for iteration variables in comprehensions *)
  ( let range = Some (Range {start=Int 1; step = Some (Int 1); end_=Int 1}) in
    let right = Syntax.Array [Compr {exp=ComponentReference (knownref 0 [cvar "i"]); idxs = [{variable = nl "i"; range}]}] in
    let eq = SimpleEquation {left = ComponentReference (knownref 0 [cfld ~known_type:FTReal "x"]); right} in
    test_norm

      "Lookup a variable bound by a comprehension"

      "package A class B Real x; equation x = {i for i in 1:1:1}; end B; end A"

      [cm "A"; cm "B"] (Has.behavior **> Has.equations **> The.first **> Is.equation (uncommented eq))
  );
  
  (
  let expected_ref = knownref 0 [cfld ~known_type:FTReal "x"] in 
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
        (Is.modified_to (Real 23.)))) ;

  
  test_norm
    "Nested redeclare extends"
    "class A13
       model B replaceable Real x; end B;
       model C replaceable model B = B; end C;
       model D extends C; redeclare model extends B end B; end D;
       model E extends D; redeclare model extends B end B; B b; Real y = b.x; end E;           
     end A13"
    [cm "A13"; cm "E";] (Has.field public "y" **> Is.bound_to **> (cre (knownref 0 [cfld "b"; cfld ~known_type:FTReal "x"]))) ;
  
  
  test_norm
    "Redeclarations in the scope of a superclass"
    "model P model M replaceable model A end A; model N A a; end N; end M;
             model M2 extends M; redeclare model A constant Real x = 42.; end A; 
                      model N2 extends N; constant Real y = a.x; end N2;
             end M2;
     end P"
    [cm "P"; cm "M2"; cm "N2"]
    (Has.field public "y" **> Is.bound_to (cre (knownref 0 [cfld "a"; cconstfld ~known_type:FTReal "x"])));

  test_norm
    "Recursive records - implemented via dynamic references"
    "package P 
     operator record A replaceable Real a; operator '*' function multiply input A a1; input A a2; output A r = A(a1.a * a2.a); end multiply; end '*'; end A;
     end P"
    [cm "P"; cm "A"; cm "'*'"; cm "multiply"]
    (Has.field public "r" **> Has.field_type (Is.class_value
                                                (Constr {arg=(DynamicReference {upref=3;base=false;downref=Name.of_list ["A"]});
                                                         constr=Cau Flags.Output}))) ;
                                                 
  test_norm
    "Recursive records"
    "package P 
     operator record A 
       replaceable Real a; 
       operator '*' 
         function multiply import P.A; 
           input A a1; 
           input A a2 = A(a = 1.0); 
           output A r = A(a1.a * a2.a); 
         end multiply; 
       end '*'; 
     end A;
     end P"
    [cm "P"; cm "A"; cm "'*'"; cm "multiply"]
    (let known_type = Some (
         FTOperatorRecord {empty_or with
                           or_tag = ".P.A";
                           or_fields = [ftarg "a" FTReal] ;
                           or_mult = [{opname="multiply";
                                       opargs=[{ftarg_name="a1";ftarg_type=FTOperatorRecordSelf ".P.A"; ftarg_opt=false};
                                               {ftarg_name="a2";ftarg_type=FTOperatorRecordSelf ".P.A"; ftarg_opt=true}]}]})
     in
     (Has.field public "r" **> Is.bound_to
        (App {fun_=rootref [cclass "P"; cclass ?known_type "A"]; named_args=[];
              args=[
                Mul {left=(cre (knownref 0 [cfld "a1"; cfld ~known_type:FTReal "a"])); right=cre (knownref 0 [cfld "a2"; cfld ~known_type:FTReal "a"])}
              ]}))) ;

  test_norm
    "Functions"
    "package P
       function F input Real x; output Real y = x; end F;
       constant Real a = F(1.0);
     end P"
    [cm "P"] (Has.field public "a" **> Is.bound_to
                (app (knownref 0 [cfunc ~known_type:(FTFunction ([{ftarg_name="x"; ftarg_type=FTReal; ftarg_opt=false}], [FTReal]))"F"]) ["", S.real 1.0])) ;

  test_norm
    "Type of Records"
    "package P
       record R Real x; end R;
       constant R a = R(x=1.0);
     end P"
    [cm "P"] (Has.field public "a" **> Is.bound_to
                (app (knownref 0 [cclass ~known_type:(FTObject [ftarg "x" FTReal]) "R"]) ["x", S.real 1.0])) ;
  
  test_norm
    "Functions with indirect input/output distinction"
    "package P
       type A = input Real;
       type B = output Real;
       function F A x; B y = x; end F;
       constant Real a = F(1.0);
     end P"
    [cm "P"] (Has.field public "a" **> Is.bound_to
                (app (knownref 0 [cfunc ~known_type:(FTFunction ([{ftarg_name="x"; ftarg_type=FTReal; ftarg_opt=false}], [FTReal]))"F"]) ["", S.real 1.0])) ;
]

let suite = "Implementation Normalization" >::: test_cases

