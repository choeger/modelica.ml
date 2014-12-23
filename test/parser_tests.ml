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
open Utils
open Batteries
open Modelica_parser
open Syntax
open Syntax_fragments
open Modelica_lexer
open Pprint_modelica

let parse_test parser input f = 
  let ucs = state_from_utf8_string input in
  let next () = next_token ucs in
  let last () = last_token ucs in
  fun () ->
  try
    f (parser "test" next last)
  with 
    SyntaxError e -> assert_failure (Printf.sprintf "Syntax Error at %s:\n%s" (show_location e) (error_message e input))
       
let expr_test input f =
  parse_test expr_parser

let parser_test_case parser lprinter sprinter input expected =
  (Printf.sprintf "Parse '%s'" input) >::: [
    ("parsing" >::
       parse_test parser input (fun e -> assert_equal ~msg:"equality of parser result" ~printer:sprinter expected e ) ) ;
     ("re-parsing" >::
        parse_test parser input
                   (fun e -> parse_test parser (lprinter e)
                                        (fun e -> assert_equal ~msg:"equality of re-parsed result" ~printer:sprinter expected e) ())) ; 
  ]

let texpr input expected = parser_test_case texpr_parser (texpr2str ~max:100) texpr2str input expected
                                            
let expr input expected = parser_test_case expr_parser (expr2str ~max:100) expr2str input expected

let stmt input expected = parser_test_case stmt_parser (stmt2str ~max:100) stmt2str input expected

let eq input expected = parser_test_case eq_parser (eq2str ~max:100) (eq2str ~max:20) input expected
                                           
let test_cases = [ 
  expr "1.234" (Real(1.234));
  expr "x" (Ide("x")) ;
  expr "new_foo" (Ide "new_foo");
  expr "1" (Int(1));

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

  expr "\"\\\"\"" (String "\"") ;

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
  
  expr ".x" (RootIde "x") ;
  expr ".x.y" (Proj {object_ = (RootIde "x"); field = "y"}) ;

  (* functions *)
  expr "f()" (App {fun_= (Ide "f"); args=[]; named_args=StrMap.empty });
  expr "f()()" (App {fun_= App { fun_=Ide "f"; args=[]; named_args=StrMap.empty }; args=[]; named_args=StrMap.empty});
  expr "f(1.0)" (App {fun_=Ide "f"; args=[Real 1.]; named_args=StrMap.empty }) ;
  expr "f(x=1.0)" (App {fun_= (Ide "f"); args=[]; named_args=StrMap.add "x" (Real 1.0) StrMap.empty });
  expr "f(1.0, x=1.0)" (App {fun_= (Ide "f"); args=[Real 1.]; named_args=StrMap.add "x" (Real 1.0) StrMap.empty });
  expr "function x" (ExplicitClosure (Ide "x"));

  (* precedences *)
  expr "1 + 2 * 3" (Plus { left = Int 1 ; right = Mul { left = Int 2 ; right = Int 3 } });
  expr "2 * 3 + 1" (Plus { left = Mul { left = Int 2 ; right = Int 3 } ; right = Int 1 });
  expr "(1 + 2) * 3" (Mul { left = Plus { left = Int 1 ; right = Int 2 } ; right = Int 3 });
  expr "3 * (1 + 2)" (Mul { right = Plus { left = Int 1 ; right = Int 2 } ; left = Int 3 });
  expr "3 * 2 ^ 4" (Mul { left = Int 3 ; right = Pow { left = Int 2 ; right = Int 4 } });
  expr "2 ^ 4 * 3" (Mul { right = Int 3 ; left = Pow { left = Int 2 ; right = Int 4 } });
  expr "-2 * 3" (UMinus (Mul { left = Int 2 ; right = Int 3 }) ) ;
  expr "-2 - 3" (Minus { left = UMinus (Int 2) ; right = Int 3 }) ;


  (* tuples and stuff *)
  expr "(1)" (Int 1) ;
  expr "()" (Empty) ;
  expr "(,)" (Tuple [Empty; Empty]);

  (* arrays *)
  expr "x[1]" (ArrayAccess { lhs = Ide "x" ; indices = [Int 1] }) ;
  expr "x[1].y" (Proj { object_ = ArrayAccess { lhs = Ide "x" ; indices = [Int 1] } ; field = "y" });
  expr "{true}" (Array [Bool true]);
  expr "[4,2;0,0]" (MArray [[Int 4; Int 2];[Int 0; Int 0]]);
    
  (* if/then *)
  expr "if true then false else true" (If { condition = Bool true; then_ = Bool false; else_if = []; else_ = Bool true });
  expr "if true then false elseif false then true else true" (If { condition = Bool true; then_ = Bool false;
                                                                   else_if = [{guard=Bool false; elsethen=Bool true}];
                                                                   else_ = Bool true });

       
  (* comprehension *)
  expr "{x for x in foo}" (Array[Compr {exp = Ide "x"; idxs = [{variable="x"; range=Some (Ide "foo")}]}]);
  expr "{x for x}" (Array [Compr {exp = Ide "x"; idxs = [{variable="x"; range=None}]}]);

  (* statements *)
  stmt "return;" (uncommented Return) ;
  stmt "break;" (uncommented Break) ;
  stmt "if true then break; end if;" (uncommented (IfStmt { condition = Bool true ; then_ = [uncommented Break] ; else_if = [] ; else_ = [] }));
  stmt "if true then break; elseif true then break; end if;" (uncommented (IfStmt { condition = Bool true ; then_ = [uncommented Break] ; else_if = [{guard=Bool true; elsethen=[uncommented Break]}] ; else_ = [] }));
  stmt "when true then break; elsewhen true then break; end when;" (uncommented (WhenStmt { condition = Bool true ; then_ = [uncommented Break] ; else_if = [{guard=Bool true; elsethen=[uncommented Break]}] ; else_ = [] }));
  stmt "f(1, x=3);" (uncommented (Call { procedure=Ide "f"; pargs = [Int 1]; pnamed_args = StrMap.add "x" (Int 3) StrMap.empty } ) );
  stmt "x := 23;" (uncommented (Assignment { target=Ide "x" ; source = Int 23 } ));
  stmt "while true loop break; break; end while;" (uncommented (WhileStmt { while_ = Bool true ; do_ = [uncommented Break; uncommented Break] ; } ) );
  stmt "for x loop break; break; end for;" (uncommented (ForStmt { idx = [{variable = "x"; range=None}] ; body = [uncommented Break; uncommented Break] ; } ) );
  stmt "for x in a loop break; break; end for;" (uncommented (ForStmt { idx = [{variable = "x"; range=Some (Ide "a")}] ; body = [uncommented Break; uncommented Break] ; } ) );

  (* equations *)
  eq "x = 0;" (uncommented (SimpleEquation { eq_lhs = Ide "x"; eq_rhs = Int 0 })) ;

  eq "if true then x.y = 0; end if;" (uncommented (IfEquation { condition= Bool true; then_ = [uncommented (SimpleEquation { eq_lhs = Proj { object_ = Ide "x"; field= "y" } ;
                                                                                                                            eq_rhs = Int 0 } )] ;
                                                                else_if = []; else_ = [];
                                                              })) ;

  eq "if c(a[i]) then a[i].p.r = {0,0,0}; end if;"  (uncommented (IfEquation {
                                                                      condition=App { fun_=Ide "c" ;
                                                                                      args=[ArrayAccess {lhs = Ide "a" ; indices = [Ide "i"]}];
                                                                                      named_args=StrMap.empty };
                                                                      then_ = [uncommented (SimpleEquation { eq_lhs = Proj { object_ = Proj { object_ =
                                                                                                                                                ArrayAccess { lhs= Ide "a";
                                                                                                                                                              indices=[Ide"i"] }; 
                                                                                                                                              field="p" } ;
                                                                                                               field = "r"
                                                                                                             } ;
                                                                                               eq_rhs = Array [Int 0; Int 0; Int 0];
                                                                                             })] ;
                                                                      else_if = []; else_ = [];
                                                                   })) ;

  eq "for i loop if true then x = 0; end if; end for;" (uncommented (ForEquation { idx= [{variable="i" ; range=None}];
                                                                                   body=[uncommented (
                                                                                             IfEquation {
                                                                                                 condition= Bool true;
                                                                                                 then_ = [uncommented (SimpleEquation { eq_lhs = Ide "x" ;
                                                                                                                                       eq_rhs = Int 0 })];
                                                                                                                      else_if = []; else_ = []
                                                                                                                      
                                                                                               })] }));
  texpr "Modelica" (TIde "Modelica");
  texpr "Modelica.Icons" (TProj {class_type=TIde "Modelica"; type_element="Icons"});
  texpr ".x" (TRootide "x");
  texpr ".x.y" (TProj { class_type=TRootide "x"; type_element= "y" });
  texpr "Modelica.Icons.InterfacesPackage" (TProj  { class_type=TProj { class_type= TIde "Modelica"; type_element="Icons"}; type_element="InterfacesPackage"});
  texpr "input Real" (TCau {flag = Input ; flagged = TIde "Real" });
  texpr "constant Real" (TVar {flag = Constant ; flagged = TIde "Real" });
  texpr "flow Real" (TCon {flag = Flow ; flagged = TIde "Real" });
  texpr "output parameter discrete stream Real" (TCau { flag = Output ; flagged = TVar { flag = Parameter ;
                                                                                         flagged =
                                                                                           TVar { flag = Discrete ;
                                                                                                  flagged =
                                                                                                    TCon { flag = Stream ;
                                                                                                           flagged = TIde "Real" } } } } ) ;
  
(*
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
