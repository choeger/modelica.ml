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

open OUnit
open Batteries
open Modelica_parser
open Syntax
open Modelica_lexer
open Pprint_modelica
       
let expr_test input f =
  let ucs = state_from_utf8_string input in
  let next () = next_token ucs in
  let last () = last_token ucs in
  fun () ->
  try
    f (expr_parser "test" next last)
  with 
    SyntaxError e -> assert_failure (Printf.sprintf "Syntax Error at %s:\n%s" (show_location e) (error_message e input))

let expr input expected = 
  (Printf.sprintf "Parse '%s'" input) >::: [
    ("parsing" >::
       expr_test input (fun e -> assert_equal ~msg:"equality of parsed expression" ~printer:expr2str expected e ) ) ;
    (* ("re-parsing" >::
       expr_test input (fun e -> expr_test (expr2str ~max:100 e) (fun e -> assert_equal ~msg:"equality of re-parsed expression" ~printer:expr2str (prep_expr expected) (prep_expr e)) ())) ; *)
  ]
      
let test_cases = [ 
  expr "1.234" (Real(1.234));
  expr "x" (Ide("x")) ;
  expr "new_foo" (Ide "new_foo");
  expr "-1" (Int(-1));

  (* TODO: copy/move to lexer test suite as approporiate *)
  expr "derfoo" (Ide "derfoo") ;
  expr "not1" (Ide "not1") ;
  expr "foo /* comment */ " (Ide "foo") ;
  expr "true" (Bool true) ;
  expr "false" (Bool false) ;
  
  expr "\"foo\"" (String "foo") ;
  
  expr "42" (Int 42) ;

  expr "42 /* the answer*/" (Int 42) ;

  expr ("42 /*" ^ (String.repeat "the answer " 10000) ^ "*/") (Int 42) ;

  expr "42 // the answer" (Int 42) ;

  expr "42.0" (Real 42.) ;

  expr "\"foo \n bar\"" (String "foo \n bar") ;

  expr "\"\\\"\"" (String "\\\"") ;

  (let x = (String.repeat "ABC" 1000) in
   expr ("\"" ^ x ^ "\"") (String x) );

  expr "x.bar" (Proj ({field = "bar"; object_=(Ide "x") }));

  expr "'foo'" (Ide "'foo'") ;

  expr "'foo' " (Ide "'foo'") ;

  expr "'foo'//bar" (Ide "'foo'") ;

  expr "'foo \\\\n'" (Ide "'foo \\\\n'") ;

  expr ":" Colon ;
  expr "der" Der ;
  expr "initial" Initial ;
  expr "end" End ;

  expr "a.b.c"  (Proj { object_ = Proj { object_ = (Ide "a"); field = "b"} ; field = "c" } );
  expr "a.'b'.c"  (Proj { object_ = Proj { object_ = (Ide "a"); field = "'b'"} ; field = "c" } ) ;
  expr "a/* comment */.b.c"  (Proj { object_ = Proj { object_ = (Ide "a"); field = "b"} ; field = "c" }) ;
  
(*
    it("Should parse root-identifier") {
      ".x" parsed_with exp should create (Root(Ide "x"))
    }

    it("Should parse root-identifiers in projections") {
      ".x.y" parsed_with exp should create (Proj(RootIde("x"), "y"))
    }

    it("Should parse an empty application") {
      "f()" parsed_with exp should create (
        App(Ide("f")))
    }

    it("Should parse two empty applications") {
      "f()()" parsed_with exp should create (
        App(App(Ide("f"))))
    }

    it("Should parse a simple application") {
      "f(1.0)" parsed_with exp should create (
        App(Ide("f"), List(RealLit(1.0))))
    }

    it("Should parse a named-arg") {
      "x=1.0" parsed_with namedArgs should create (Map("x" -> RealLit(1.0)))
    }

    it("Should parse a named-arg application") {
      "f(x=1.0)" parsed_with exp should create (
        App(Ide("f"), Nil, Map("x" -> RealLit(1.0)) ) )
    }

    it("Should parse a mixed application") {
      "f(1.0, x=1.0)" parsed_with exp should create (
        App(Ide("f"), List(RealLit(1.0)), Map("x" -> RealLit(1.0))))
    }
    
    it("Should bind multiplication over addition") {
      "1 + 2 * 3" parsed_with exp should create(Plus(IntLit(1), Mul(IntLit(2), IntLit(3))))
      "2 * 3 + 1" parsed_with exp should create(Plus(Mul(IntLit(2), IntLit(3)),IntLit(1)))
    }
    
    it("Should respect parentheses") {
      "(1 + 2) * 3" parsed_with exp should create(Mul(Plus(IntLit(1), IntLit(2)), IntLit(3)))
      "3 * (1 + 2)" parsed_with exp should create(Mul(IntLit(3), Plus(IntLit(1), IntLit(2))))
    }

    it("Should bind exponentiation over addition") {
      "1 + 2 * 3 ^ 4" parsed_with exp should create(Plus(IntLit(1), Mul(IntLit(2), Pow(IntLit(3), IntLit(4)))))
      "3 ^ 4 * 2 + 1" parsed_with exp should create(Plus(Mul(Pow(IntLit(3), IntLit(4)), IntLit(2)), IntLit(1)))
    }

    it("Should bind negation less strongly than multiplication") {
      "-2 * 3" parsed_with exp should create(UMinus(Mul(IntLit(2), IntLit(3))))
    }

    it("Should parse negations alongside subtraction") {
      "-2 - 3" parsed_with exp should create(Minus(UMinus(IntLit(2)), IntLit(3)))
    }

    it("Should not create 1-tuples") {
      "(1)" parsed_with exp should create (IntLit(1))
    }

    it("Should create empty tuples (for pattern-expressions)") {
      "()" parsed_with exp should create (Empty)
    }

    it("Should create tuples containing empty-vars (for pattern-expressions)") {
      "(,)" parsed_with exp should create (Tup(List(Empty,Empty)))
    }

    it("Should parse array-access") {
      "x[1]" parsed_with exp should create (ArrAcc(Ide("x"),List(IntLit(1))))
    }

    it("Should parse nested array-access") {
      "x[1].y" parsed_with exp should create (Proj(ArrAcc(Ide("x"),List(IntLit(1))),"y"))
    }

    it("Should parse if-expressions ") {
      "if true then false else true" parsed_with exp should create (If(BoolLit(true), BoolLit(false), BoolLit(true)))
    }

    it("Should parse else-if-expressions ") {
      "if true then false elseif false then true else true" parsed_with exp should create (If(BoolLit(true), BoolLit(false), BoolLit(true), List((BoolLit(false),BoolLit(true))) ))
    }

    it("Should parse array constructions ") {
      "{true}" parsed_with exp should create (Array(List(BoolLit(true))))
    }

    it("Should parse list comprehensions") {
      "{x for x in foo}" parsed_with exp should create (Array(List(Compr(Ide("x"), List(Idx("x", Some(Ide("foo"))))))))
    }

    it("Should parse slightly complicated list comprehensions") {
      "{1, 2, x for x in foo}" parsed_with exp should create (Array(List(IntLit(1), IntLit(2), Compr(Ide("x"), List(Idx("x", Some(Ide("foo"))))))))
    }

    it("Should parse list comprehension in function application") {
      "f(x for x)" parsed_with exp should create (App(Ide("f"), List(Compr(Ide("x"), List(Idx("x"))))))
    }
    
    it("Should parse the explicit partial function expression") {
      "function x" parsed_with exp should create(ExplicitPartialFunction(Ide("x")))
    }

    it("Should parse matrix constructions ") {
      "[4,2;0,0]" parsed_with exp should create (MArray(List(List(IntLit(4), IntLit(2)), List(IntLit(0), IntLit(0))) ))
    }

    it("Should parse return statements") {
      "return;" parsed_with statement should create (Return())
    }

    it("Should parse break statements") {
      "break;" parsed_with statement should create (Break())
    }

    it("Should parse simple if-then statements") {
      "if true then break; end if;" parsed_with statement should create (IfStmt(BoolLit(true), List(Break())))
    }

    it("Should parse application statements") {
      "f();" parsed_with statement should create (ExprStmt(App(Ide("f"))))
    }

    it("Should parse equations") {
      "x = 0;" parsed_with equation should create (
        SimpleEquation(Ide("x"), IntLit(0))
      )
    }    

    it("Should parse if-equations") {
      "if true then x.y = 0; end if;" parsed_with equation should create (
        IfEquation(BoolLit(true), SimpleEquation(Proj(Ide("x"),"y"), IntLit(0))::Nil)
      )
    }    

    it("Should parse slighty complex if-equations") { // a[i].d.d = 0;
      "if c(a[i]) then a[i].p.r = {0,0,0}; end if;" parsed_with equation should create (
        IfEquation(App(Ide("c"), List(ArrAcc(Ide("a"), List(Ide("i"))))), 
                   SimpleEquation(Proj(Proj(ArrAcc(Ide("a"), List(Ide("i"))),"p"),"r"),
                                  Array(List(IntLit(0),IntLit(0),IntLit(0))))::Nil)
      )

    }

    it("Should parse nested for/if equations") {
      "for i loop if true then x = 0; end if; end for;" parsed_with equation should create (
        ForEquation(List(Idx("i", None)), IfEquation(BoolLit(true), SimpleEquation(Ide("x"), IntLit(0))::Nil)::Nil)
      )
    }

    it ("Should parse type-ide's") {
      "Modelica" parsed_with type_exp should create (TIde("Modelica"))
    }

    it ("Should parse type-names") {
      "Modelica.Icons" parsed_with type_exp should create (TProj(TIde("Modelica"), "Icons"))
    }

    it("Should parse type root-identifiers") {
      ".x" parsed_with type_exp should create (TRootIde("x"))
    }

    it("Should parse root-identifiers in type-projections") {
      ".x.y" parsed_with type_exp should create (TProj(TRootIde("x"), "y"))
    }

    it ("Should parse longer type-names") {
      "Modelica.Icons.InterfacesPackage" parsed_with type_exp should create (TProj(TProj(TIde("Modelica"), "Icons"),"InterfacesPackage"))
    }

    it ("Should parse unnamed imports") {
      "import X;" parsed_with _import should create (UnnamedImport(List("X")))
    }

    it ("Should parse named imports") {
      "import Y=X;" parsed_with _import should create (NamedImport("Y", List("X")))
    }

    it ("Should parse qualified imports") {
      "import X.*;" parsed_with _import should create (UnqualifiedImport(List("X")))
    }

    it("Should parse extends-statements") {
      "extends Modelica.Icons.InterfacesPackage;" parsed_with _extends(Public) should create (
        Extend(TProj(TProj(TIde("Modelica"), "Icons"),"InterfacesPackage")))
    }

    it("Should parse a simple component") {
      "parameter FluidHeatFlow.Media.Medium medium;" parsed_with _def(Public) should create (
        List(Def("medium", TVariability(Parameter, TProj(TProj(TIde("FluidHeatFlow"), "Media"), "Medium")))))
    }

    it("Should parse component-comments") {
      "parameter Modelica.SIunits.Density rho=1.225 \"Air Density\";" parsed_with _def(Public) should create (
        List(Def("rho", TVariability(Parameter, TProj(TProj(TIde("Modelica"), "SIunits"), "Density")), None,
                 Some(RealLit(1.225)), None, DefOptions(), Comment(Some("Air Density")))))
    }

    it("Should parse typedef-comments") {
      """class A "Test" end A;""" parsed_with typedef should create (
        TypeDef(name = "A", rhs = Composition(), comment = Comment(Some("Test")))
      )
    }


    it("Should parse component comments on matrix definitions") {
      "parameter Real friction_pos[:, 2]=[0, 1] \"[w,tau] positive sliding friction characteristic (w>=0)\";" parsed_with 
        _def(Public) should create (
          List(Def("friction_pos", TArrayExp(TVariability(Parameter,TIde("Real")),List(Colon, IntLit(2))), None,
                 Some(MArray(List(List(IntLit(0),IntLit(1))))), None, DefOptions(), Comment(Some("[w,tau] positive sliding friction characteristic (w>=0)"))))
          )
    }


    it("Should parse a simple definition") {
      "parameter FluidHeatFlow.Media.Medium medium := FluidHeatFlow.Media.Medium();" parsed_with _def(Public) should create(
        List(Def("medium", TVariability(Parameter, TProj(TProj(TIde("FluidHeatFlow"), "Media"), "Medium")), None, Some(App(Proj(Proj(Ide("FluidHeatFlow"),"Media"),"Medium"))))))
    }

    it("Should parse constrained component declarations") {
      "replaceable T t constrainedby S;" parsed_with _def(Public) should create (
        List(Def("t", TIde("T"), Some(Constraint(TIde("S"))), options = DefOptions(replaceable = true) ))
      )
    }

    it("Should parse flags") {
      "partial" parsed_with flag("partial ") should create (true)
    }

    it("Should parse partial models") {
      "partial model A end A;" parsed_with typedef should create (TypeDef("A", Model, Composition(), options=TypeDefOptions(partial=true)))
    }

    it("Should parse replaceable models") {
      "replaceable model A end A;" parsed_with typedef should create (TypeDef("A", Model, Composition(), options=TypeDefOptions(replaceable=true)))
    }

    it("Should parse encapsulated models") {
      "encapsulated model A end A;" parsed_with typedef should create (TypeDef("A", Model, Composition(), options=TypeDefOptions(encapsulated=true)))
    }

    it("Should parse replaceable encapsulated partial models") {
      "replaceable encapsulated partial model A end A;" parsed_with typedef should create (TypeDef("A", Model, Composition(), options=TypeDefOptions(replaceable=true, partial = true, encapsulated=true)))
    }

    it("Should parse lexical redeclarations") {
      "model X redeclare type T = S; end X;" parsed_with typedef should create (
        TypeDef("X", Model, Composition(redeclared_types = TypeDef("T", Type, TIde("S"))::Nil))
        )
    }
      
    it("Should parse enumerations") {
      "type E = enumeration(x);" parsed_with typedef should create (
        TypeDef("E", Type, Enumeration(EnumLiteral("x")::Nil))
        )
    }

    it("Should parse constrained types") {
      "type E = A constrainedby B;" parsed_with typedef should create (
        TypeDef("E", Type, TIde("A"), Some(Constraint(TIde("B"))))
        )
    }

    it("Should parse equations as payload of type-definitions") {
      "class X equation 1 = 1; end X;" parsed_with typedef should create (
        TypeDef("X", Class, Composition(cargo = Behavior(equations = SimpleEquation(IntLit(1), IntLit(1))::Nil)))
      )
    }

    it("Should parse external definitions") {
      "function f external \"C\" f(); end f;" parsed_with typedef should create (
        TypeDef("f", Function, Composition(cargo = Behavior(external = Some(ExternalDef("C", None, App(Ide("f"))))) ))
      )
    }

    it("Should parse the encapsulated flag") {
      "encapsulated class X end X;" parsed_with typedef should create (
        TypeDef("X", Class, Composition(), None, TypeDefOptions(encapsulated=true))
      )
    }

    val line_annotation = Mod(redefs = Redef(name = List("Line"), mod = Some(
          Mod(redefs = Redef(name=List("points"), rhs=Some(Array(List(
            /* points */
            Array(List(UMinus(IntLit(19)), UMinus(IntLit(10)))), 
            Array(List(IntLit(20), UMinus(IntLit(10)))), 
            Array(List(IntLit(20), UMinus(IntLit(6)))), 
            Array(List(IntLit(38), UMinus(IntLit(6))))
          ))))::Redef(name=List("color"), rhs=Some(
            /* color */
            Array(List(IntLit(255), IntLit(0), IntLit(255))))
          )::Nil)))::Nil)

    it("Should parse an annotation") {
      "annotation (Line(points={{-19,-10},{20,-10}, {20,-6},{38,-6}}, color={255,0,255}))" parsed_with annotation should create (
        line_annotation
      )
    }

    it("Should parse a connect-statement with an annotation") {
      "connect(not1.y, rSFlipFlop.R) annotation (Line(points={{-19,-10},{20,-10}, {20,-6},{38,-6}}, color={255,0,255}));" parsed_with equation should create (
        ExpEquation(App(Ide("connect"), List(Proj(Ide("not1"), "y"), Proj(Ide("rSFlipFlop"), "R"))), Comment(annotation = Some(line_annotation)))
      )
    }*)

]
						  
let suite = "Parser" >::: test_cases
