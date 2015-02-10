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
open Location
       
let parse_test parser input f = 
  let ucs = state_from_utf8_string "test input" input in
  let next () = next_token ucs in
  let last () = last_token ucs in
  fun () ->
  try
    f (parser next last)
  with 
    SyntaxError e -> assert_failure (Printf.sprintf "Syntax Error at %s:\n%s" (show_location e) (error_message e input))
       
let expr_test input f =
  parse_test expr_parser

let nl = mknoloc
           
let parser_test_case parser lprinter sprinter prep input expected =
  (Printf.sprintf "Parse '%s'" input) >::: [
    ("parsing" >::
       parse_test parser input (fun e -> assert_equal ~msg:"equality of parser result" ~printer:sprinter expected (prep e) ) ) ;
     ("re-parsing" >::
        parse_test parser input
                   (fun firstpass -> parse_test parser (lprinter firstpass)
                                        (fun e -> assert_equal ~msg:"equality of re-parsed result" ~printer:sprinter (prep firstpass) (prep e)) ())) ; 
  ]
                                             
let erase_location = { Traversal.default_mapper with Mapper.map_location = (fun _ _ -> Location.none) }

let prep_import = erase_location.map_import erase_location 
                       
let import input expected = parser_test_case import_parser (import2str ~max:100) import2str prep_import input expected 

let prep_extend = erase_location.map_extend erase_location 

let extend input expected = parser_test_case extends_parser (extend2str ~max:100) extend2str prep_extend input expected

let prep_texpr = erase_location.map_texp erase_location 

let texpr input expected = parser_test_case texpr_parser (texpr2str ~max:100) texpr2str prep_texpr input expected
                                            
let prep_expr = erase_location.map_exp erase_location 

let expr input expected = parser_test_case expr_parser (expr2str ~max:100) expr2str prep_expr input expected

let prep_stmt = erase_location.map_statement erase_location 

let stmt input expected = parser_test_case stmt_parser (stmt2str ~max:100) stmt2str prep_stmt input expected

let prep_eq = erase_location.map_equation erase_location 

let eq input expected = parser_test_case eq_parser (eq2str ~max:100) (eq2str ~max:20) prep_eq input expected

let prep_defs = Mapper.map_list erase_location.map_def erase_location 

let defs input expected = parser_test_case defs_parser (defs2str ~max:100) (defs2str ~max:20) prep_defs input expected

let prep_typedef = erase_location.map_typedef erase_location 

let typedef input expected = parser_test_case td_parser (td2str ~max:100) (td2str ~max:20) prep_typedef input expected
                                           
let test_cases = [ 
  expr "1.234" (Real(1.234));
  expr "10e2" (Real(1000.));
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
  expr "assert" Assert ;
  
  expr "a.b.c"  (Proj { object_ = Proj { object_ = (Ide "a"); field = "b"} ; field = "c" } );
  expr "a.'b'.c"  (Proj { object_ = Proj { object_ = (Ide "a"); field = "'b'"} ; field = "c" } ) ;
  expr "a/* comment */.b.c"  (Proj { object_ = Proj { object_ = (Ide "a"); field = "b"} ; field = "c" }) ;
  
  expr ".x" (RootIde "x") ;
  expr ".x.y" (Proj {object_ = (RootIde "x"); field = "y"}) ;

  (* functions *)
  expr "f()" (App {fun_= (Ide "f"); args=[]; named_args=[] });
  expr "f()()" (App {fun_= App { fun_=Ide "f"; args=[]; named_args=[] }; args=[]; named_args=[]});
  expr "f(1.0)" (App {fun_=Ide "f"; args=[Real 1.]; named_args=[] }) ;
  expr "f(x=1.0)" (App {fun_= (Ide "f"); args=[]; named_args=[named "x" (Real 1.0)]});
  expr "f(1.0, x=1.0)" (App {fun_= (Ide "f"); args=[Real 1.]; named_args=[named "x" (Real 1.0)]});
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

  expr "-2 * 3 < 2*3" (Lt {left= UMinus (Mul { left = Int 2 ; right = Int 3 }) ; right=Mul { left = Int 2 ; right = Int 3 } } ) ;
  expr "-2 * 3 > 2*3" (Gt {left= UMinus (Mul { left = Int 2 ; right = Int 3 }) ; right=Mul { left = Int 2 ; right = Int 3 } } ) ;
  expr "-2 * 3 <= 2*3" (Leq {left= UMinus (Mul { left = Int 2 ; right = Int 3 }) ; right=Mul { left = Int 2 ; right = Int 3 } } ) ;
  expr "-2 * 3 >= 2*3" (Geq {left= UMinus (Mul { left = Int 2 ; right = Int 3 }) ; right=Mul { left = Int 2 ; right = Int 3 } } ) ;
  expr "-2 * 3 <> 2*3" (Neq {left= UMinus (Mul { left = Int 2 ; right = Int 3 }) ; right=Mul { left = Int 2 ; right = Int 3 } } ) ;
  expr "-2 * 3 == 2*3" (Eq {left= UMinus (Mul { left = Int 2 ; right = Int 3 }) ; right=Mul { left = Int 2 ; right = Int 3 } } ) ;

  expr "1 < 2 and 2 < 3" (And {left= (Lt { left = Int 1 ; right = Int 2 }) ; right=Lt { left = Int 2 ; right = Int 3 } }) ;
  expr "1 < 2 or 2 < 3" (Or {left= (Lt { left = Int 1 ; right = Int 2 }) ; right=Lt { left = Int 2 ; right = Int 3 } }) ;
  expr "1 < 2 and x or y" (Or {left=And {left= (Lt { left = Int 1 ; right = Int 2 }) ; right=Ide "x" }; right=Ide "y"}) ;

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
  expr "{x for x in foo}" (Array[Compr {exp = Ide "x"; idxs = [{variable=nl "x"; range=Some (Ide "foo")}]}]);
  expr "{x for x}" (Array [Compr {exp = Ide "x"; idxs = [{variable=nl "x"; range=None}]}]);

  (* statements *)
  stmt "return;" (uncommented Return) ;
  stmt "break;" (uncommented Break) ;
  stmt "assert();" (uncommented (Call {procedure=Assert; pargs=[]; pnamed_args = [] }));
  stmt "print(\"... testAllFunctions(..) is logged in \" + file);"
       (uncommented (Call {procedure=Ide"print" ; pargs = [
                             Plus { left=String "... testAllFunctions(..) is logged in "; right = Ide "file" }
                           ]; pnamed_args =  [] }));
  
  stmt "if true then break; end if;" (uncommented (IfStmt { condition = Bool true ; then_ = [uncommented Break] ; else_if = [] ; else_ = [] }));
  stmt "if true then break; elseif true then break; end if;" (uncommented (IfStmt { condition = Bool true ; then_ = [uncommented Break] ; else_if = [{guard=Bool true; elsethen=[uncommented Break]}] ; else_ = [] }));
  stmt "when true then break; elsewhen true then break; end when;" (uncommented (WhenStmt { condition = Bool true ; then_ = [uncommented Break] ; else_if = [{guard=Bool true; elsethen=[uncommented Break]}] ; else_ = [] }));
  stmt "f(1, x=3);" (uncommented (Call { procedure=Ide "f"; pargs = [Int 1]; pnamed_args = [named "x" (Int 3)]} ) );
  stmt "x := 23;" (uncommented (Assignment { target=Ide "x" ; source = Int 23 } ));
  stmt "(,) := 23;" (uncommented (Assignment { target=OutputExpression [None; None] ; source = Int 23 } ));
  stmt "() := 23;" (uncommented (Assignment { target=OutputExpression [None] ; source = Int 23 } ));  
  stmt "(x,,y) := 23;" (uncommented (Assignment { target=OutputExpression([Some (Ide "x");None;Some (Ide "y")]) ; source = Int 23 } ));  
  stmt "while true loop break; break; end while;" (uncommented (WhileStmt { while_ = Bool true ; do_ = [uncommented Break; uncommented Break] ; } ) );
  stmt "for x loop break; break; end for;" (uncommented (ForStmt { idx = [{variable = nl "x"; range=None}] ; body = [uncommented Break; uncommented Break] ; } ) );
  stmt "for x in a loop break; break; end for;" (uncommented (ForStmt { idx = [{variable = nl "x"; range=Some (Ide "a")}] ; body = [uncommented Break; uncommented Break] ; } ) );

  (* equations *)
  eq "x = 0;" (uncommented (SimpleEquation { left = Ide "x"; right = Int 0 })) ;

  eq "if true then x.y = 0; end if;" (uncommented (IfEquation { condition= Bool true; then_ = [uncommented (SimpleEquation { left = Proj { object_ = Ide "x"; field= "y" } ;
                                                                                                                            right = Int 0 } )] ;
                                                                else_if = []; else_ = [];
                                                              })) ;

  eq "if c(a[i]) then a[i].p.r = {0,0,0}; end if;"  (uncommented (IfEquation {
                                                                      condition=App { fun_=Ide "c" ;
                                                                                      args=[ArrayAccess {lhs = Ide "a" ; indices = [Ide "i"]}];
                                                                                      named_args=[] };
                                                                      then_ = [uncommented (SimpleEquation { left = Proj { object_ = Proj { object_ =
                                                                                                                                                ArrayAccess { lhs= Ide "a";
                                                                                                                                                              indices=[Ide"i"] }; 
                                                                                                                                              field="p" } ;
                                                                                                               field = "r"
                                                                                                             } ;
                                                                                               right = Array [Int 0; Int 0; Int 0];
                                                                                             })] ;
                                                                      else_if = []; else_ = [];
                                                                   })) ;

  eq "for i loop if true then x = 0; end if; end for;" (uncommented (ForEquation { idx= [{variable=nl "i" ; range=None}];
                                                                                   body=[uncommented (
                                                                                             IfEquation {
                                                                                                 condition= Bool true;
                                                                                                 then_ = [uncommented (SimpleEquation { left = Ide "x" ;
                                                                                                                                       right = Int 0 })];
                                                                                                                      else_if = []; else_ = []
                                                                                                                      
                                                                                               })] }));
  eq "x = 23;" (uncommented (SimpleEquation { left=Ide "x" ; right = Int 23 } ));
  eq "(,) = 23;" (uncommented (SimpleEquation { left=OutputExpression [None; None] ; right = Int 23 } ));
  eq "() = 23;" (uncommented (SimpleEquation { left=OutputExpression [None] ; right = Int 23 } ));  
  eq "(x,,y) = 23;" (uncommented (SimpleEquation { left=OutputExpression([Some (Ide "x");None;Some (Ide "y")]) ; right = Int 23 } ));  


  texpr "Modelica" (type_name ["Modelica"]);
  texpr "Modelica.Icons" (type_name ["Modelica";"Icons"]);
  texpr ".x" (root_type ["x"]);
  texpr ".x.y" (root_type ["x";"y"]);
  texpr "Modelica.Icons.InterfacesPackage" (type_name ["Modelica";"Icons";"InterfacesPackage"]);
  texpr "input Real" (TCau {flag = Input ; flagged = type_name ["Real"] });
  texpr "constant Real" (TVar {flag = Constant ; flagged = type_name ["Real"] });
  texpr "flow Real" (TCon {flag = Flow ; flagged = type_name ["Real"] });
  texpr "output parameter discrete stream Real" (TCau { flag = Output ; flagged = TVar { flag = Parameter ;
                                                                                         flagged =
                                                                                           TVar { flag = Discrete ;
                                                                                                  flagged =
                                                                                                    TCon { flag = Stream ;
                                                                                                           flagged = type_name ["Real"] } } } } ) ;
  texpr "Real[2,3]" (TArray {base_type = type_name ["Real"]; dims = [Int 2 ; Int 3]} ) ;
  texpr "T()" (TMod { mod_type = type_name ["T"] ; modification = no_modification } ) ;
  

  import "import X" (uncommented (Unnamed [nl "X"])) ;
  import "import Y=X" (uncommented (NamedImport {global = [nl "X"] ; local = nl "Y" }));
 
  import "import X.*" (uncommented (UnqualifiedImport [nl "X"]));


  (let extend_statement = { ext_type = (type_name ["Modelica";"Icons";"InterfacesPackage"]) ;
                            ext_annotation = None }
   in
   extend "extends Modelica.Icons.InterfacesPackage" extend_statement );

  defs "Real p" [uncommented {empty_def with def_name = "p" ; def_type = type_name ["Real"] ;}] ;
  defs "Real p, q" [uncommented {empty_def with def_name = "p" ; def_type = type_name ["Real"] ;} ;
                    uncommented {empty_def with def_name = "q" ; def_type = type_name ["Real"] ;}
                   ] ;  

  
  defs "parameter FluidHeatFlow.Media.Medium medium" [uncommented { empty_def with def_name = "medium" ;
                                                                                   def_type = TVar { flag = Parameter ;
                                                                                                     flagged =
                                                                                                       type_name ["FluidHeatFlow";
                                                                                                                  "Media";
                                                                                                                  "Medium"];
                                                                                                   }
                                                                  }];
                                                                                   
  defs "Medium medium := Medium()" [uncommented { empty_def with def_name = "medium" ;
                                                                 def_type = type_name ["Medium"] ;
                                                                 def_rhs = Some ( App ( empty_app (Ide "Medium") ) ) ;
                                                }] ;

  
  defs "replaceable T t constrainedby S" [uncommented { empty_def with def_name = "t" ;
                                                                       def_type = type_name ["T"] ;
                                                                       def_constraint = Some (uncommented ( type_name ["S"])) ;
                                                                       def_options = { no_def_options with replaceable = true } ;
                                                      }] ;


  defs "Density rho=1.225 \"Air Density\"" [{ commented = { empty_def with def_name = "rho";
                                                                           def_type = type_name ["Density"];
                                                                           def_rhs = Some (Real 1.225) ;
                                                          } ;
                                              comment = unannotated ( Some (nl "Air Density")  )}];
  

  defs "Real friction_pos[:, 2]=[0; 1] \"[w,tau] positive sliding friction characteristic (w>=0)\""
       [{ commented = { empty_def with def_name = "friction_pos";
                                       def_type = TArray { base_type=type_name ["Real"]; dims = [Colon ; Int 2] } ;
                                       def_rhs = Some (MArray [[Int 0];[Int 1]]) ;
                      } ;
          comment = unannotated ( Some (nl "[w,tau] positive sliding friction characteristic (w>=0)") ) 
        }];

  typedef "type T = A" (uncommented (Short { empty_typedef with td_name = nl "T" ; type_exp = type_name ["A"] })) ;

  (let def = uncommented { empty_def with def_name = "x" ; def_type = type_name ["S"] } in
   typedef "class T S x; end T" (uncommented (Composition { empty_typedef with td_name = nl"T" ;
                                                                               type_exp = {empty_composition with public = {
                                                                                            empty_elements with
                                                                                            defs = [def] } };
                                                                               sort = Class ;
                                                          } )));

  (let def = uncommented { empty_def with def_name = "x" ; def_type = type_name ["S"] } in
               typedef "class T \"comment\" S x; end T" { commented = Composition { empty_typedef with td_name = nl"T" ;
                                                                                                       type_exp = {
                                                                                                         empty_composition with
                                                                                                         public = { empty_elements with
                                                                                                                    defs = [def] }};
                                                                                           sort = Class ;
                                                                      } ;
                                              comment = unannotated ( Some (nl "comment") ) ;
                                            } );
  
  typedef "partial model A end A" (uncommented (Composition { empty_typedef with td_name = nl"A" ;
                                                                               type_exp = empty_composition;
                                                                               sort = Model ;
                                                                               type_options = { no_type_options with partial = true };
                                                             } ));

  typedef "replaceable model A end A" (uncommented (Composition { empty_typedef with td_name = nl"A" ;
                                                                                     type_exp = empty_composition;
                                                                                     sort = Model ;
                                                                                     type_options = {
                                                                                       no_type_options with type_replaceable = true };
                                                                } ));

  typedef "replaceable package A end A" (uncommented (Composition { empty_typedef with td_name = nl"A" ;
                                                                                       type_exp = empty_composition;
                                                                                       sort = Package ;
                                                                                       type_options = {
                                                                                       no_type_options with type_replaceable = true };
                                                                } ));

  
  typedef "encapsulated model A end A" (uncommented (Composition { empty_typedef with td_name = nl"A" ;
                                                                                       type_exp = empty_composition;
                                                                                       sort = Model ;
                                                                                       type_options = {
                                                                                         no_type_options with encapsulated = true };
                                                                  } ));

  typedef "replaceable encapsulated partial model A end A"
          (uncommented (Composition { empty_typedef with td_name = nl"A" ;
                                                         type_exp = empty_composition;
                                                         sort = Model ;
                                                         type_options = {
                                                           no_type_options with encapsulated = true ;
                                                                                partial = true ;
                                                                                type_replaceable = true ;
                                                         };
                                                         
                                    } ));


  typedef "model X redeclare type T = S; end X"
          (uncommented (Composition { empty_typedef with td_name = nl"X" ;
                                                         type_exp = { empty_composition with
                                                                      public = { empty_elements with
                                                                                 redeclared_types = [
                                                                                 uncommented (
                                                                                     Short { empty_typedef with td_name = nl"T" ;
                                                                                                                type_exp = type_name ["S"]
                                                                                           }
                                                                                   )] } 
                                                                    } ;
                                                         sort = Model ;
                                    } ));

  typedef "model X replaceable package T = S; end X"
          (uncommented (Composition { empty_typedef with td_name = nl"X" ;
                                                         type_exp = { empty_composition with
                                                                      public = { empty_elements with
                                                                      typedefs = [ uncommented (
                                                                                       Short { empty_typedef with td_name = nl"T" ;
                                                                                                                  type_exp = type_name ["S"] ;
                                                                                                                  sort = Package ;
                                                                                                                  type_options = {
                                                                                                                    no_type_options with
                                                                                                                    type_replaceable =
                                                                                                                      true
                                                                                                                  }
                                                                                             })]} ;
                                                                    } ;
                                                         sort = Model ;
                                    } ));
  
  typedef "model X equation 1 = 1; end X"
          (uncommented (Composition { empty_typedef with td_name = nl"X" ;
                                                         type_exp = { empty_composition with
                                                                      cargo = { empty_behavior with
                                                                                equations = [ uncommented (
                                                                                                  SimpleEquation {
                                                                                                      left=Int 1;
                                                                                                      right=Int 1}
                                                                                                )]
                                                                              } ;
                                                                    } ;
                                                         sort = Model ;
                                    } ));
  
  typedef "model X annotation ();  end X"
          ({commented = (Composition { empty_typedef with td_name = nl"X" ;
                                                         type_exp = empty_composition ;
                                                         sort = Model ;
                                    }) ;
            comment = {annotated_elem = None; annotation = Some no_modification }
           });
  
  
  typedef "type E = enumeration(x)" (uncommented (Enumeration {empty_typedef with td_name = nl "E" ;
                                                                                  type_exp = [uncommented "x"];

                                                              } )) ;

  typedef "type E = enumeration(:)" (uncommented (OpenEnumeration {empty_typedef with td_name = nl "E" ;
                                                                                      type_exp = ();
                                                                                      
                                                                  } )) ;

  typedef "type E = der(foo.bar, x, y)" (uncommented (DerSpec {empty_typedef with td_name = nl "E" ;
                                                                                  type_exp = { der_name = [nl "foo"; nl "bar"];
                                                                                               idents = [nl "x";nl "y"] }
                                                                                      
                                                                  } )) ;
  typedef "class extends X Real p; end X"
          (uncommented (Extension {empty_typedef with td_name = nl"X" ;
                                                      sort = Class ;
                                                      type_exp = ({ empty_composition with
                                                                    public = { empty_elements with 
                                                                               defs = [uncommented
                                                                                         {empty_def with def_name = "p" ;
                                                                                                         def_type = type_name ["Real"] ;}] ;
                                                                             }
                                                                  }, None);
                                  }));
                                  
  

  typedef "function f external \"C\" f(); end f"
          (uncommented (Composition {
                            empty_typedef with td_name = nl"f" ;
                                               type_exp = { empty_composition with
                                                            cargo = { empty_behavior with
                                                                      external_ = Some (
                                                                                      unannotated {
                                                                                          lang="C" ;
                                                                                          ext_lhs=None;
                                                                                          ext_ident = "f";
                                                                                          ext_args = []
                                                                                        }
                                                                                    )
                                                                    } ;
                                                          } ;
                                               sort = Function } ));
                                                                            
  typedef "function f external \"C\" x = f(); end f"
          (uncommented (Composition { empty_typedef with td_name = nl"f" ;
                                                         type_exp = { empty_composition with
                                                                      cargo = { empty_behavior with
                                                                                external_ = Some (
                                                                                                unannotated {
                                                                                                    lang="C" ;
                                                                                                    ext_lhs=Some (Ide "x");
                                                                                                    ext_ident = "f";
                                                                                                    ext_args = []
                                                                                                  }
                                                                                              )
                                                                              } ;
                                                                    } ;
                                                         sort = Function } ));

  typedef "type A = B(redeclare type C = D)"
          (uncommented (Short { empty_typedef with
                                td_name = nl"A" ;
                                type_exp = TMod { mod_type=type_name ["B"] ;
                                                  modification = { no_modification with
                                                                   types = [{ redecl_each = false ;
                                                                              redecl_type =
                                                                                uncommented ({
                                                                                              empty_typedef with
                                                                                              td_name = nl"C" ;
                                                                                              type_exp = type_name ["D"]
                                                                                            })
                                                                            }]}
                                                }
                              }));                                                                 
  
  typedef "type A = B(replaceable type C = D)"
          (uncommented (Short { empty_typedef with
                                td_name = nl"A" ;
                                type_exp = TMod { mod_type=type_name ["B"] ;
                                                  modification = {
                                                    no_modification with
                                                    types = [{ redecl_each = false ;
                                                               redecl_type =
                                                                 uncommented { empty_typedef with
                                                                               td_name = nl"C" ;
                                                                               type_exp = type_name ["D"] ;
                                                                               type_options = {
                                                                                 no_type_options with
                                                                                 type_replaceable = true;
                                                                               }
                                                                             }
                                                             }];}
                                                }
                              }));             

  typedef "type A = B(redeclare C c)"
          (uncommented (Short { empty_typedef with
                                td_name = nl"A" ;
                                type_exp = TMod { mod_type=type_name ["B"] ;
                                                  modification = { no_modification with
                                                                   components = [{ each = false ;
                                                                                   def = 
                                                                                     uncommented ({
                                                                                              empty_def with
                                                                                              def_name = "c" ;
                                                                                              def_type = type_name ["C"]
                                                                                            })
                                                                            }]}
                                                }
                              }));                                                                 

  typedef "type A = B(replaceable C c)"
          (uncommented (Short { empty_typedef with
                                td_name = nl"A" ;
                                type_exp = TMod { mod_type=type_name ["B"] ;
                                                  modification = { no_modification with
                                                                   components = [{ each = false ;
                                                                                   def = 
                                                                                     uncommented ({
                                                                                              empty_def with
                                                                                              def_name = "c" ;
                                                                                              def_type = type_name ["C"];
                                                                                              def_options = { no_def_options with
                                                                                                              replaceable=true }
                                                                                            })
                                                                            }]}
                                                }
                              }));

  typedef "function f algorithm print(\"hello, world!\"); end f"
          (uncommented
             (Composition { empty_typedef with td_name = nl "f" ;
                                               type_exp = { empty_composition with
                                                            cargo = { empty_behavior with
                                                                      algorithms = [[uncommented (
                                                                                       Call {procedure=Ide "print" ;
                                                                                            pargs = [String "hello, world!"] ;
                                                                                            pnamed_args = [] } ) ]];
                                                                    } ;
                                                          } ;
                                               sort = Function } ));
  
  (let line = {
     no_modification
   with modifications =
          [uncommented {mod_each=false;mod_final=false;
                        mod_name=[nl "Line"];
                        mod_value=Some (Nested {no_modification with
                                                 modifications =
                                                   [uncommented {mod_each=false;mod_final=false;
                                                                 mod_name=[nl "points"];
                                                                 mod_value= Some (Rebind (
                                                                                      Array [
                                                                                          Array [UMinus (Int 19); UMinus (Int 10)];
                                                                                          Array [Int 20;UMinus (Int 10)];
                                                                                          Array [Int 20;UMinus (Int 6)];
                                                                                          Array [Int 38;UMinus (Int 6)];
                                                                                        ]));
                                                                };
                                                    uncommented {mod_each=false;mod_final=false;
                                                                 mod_name=[nl "color"];
                                                                 mod_value=Some (Rebind (Array [Int 255;Int 0;Int 255]));
                                                                }
                                                   ]})
                       }]}
   in
   let annotation = Some line in
   eq "connect(not1.y, rSFlipFlop.R) annotation (Line(points={{-19,-10},{20,-10}, {20,-6},{38,-6}}, color={255,0,255}));" 
      { commented = ExpEquation (App {(empty_app (Ide "connect")) with args=[name ["not1";"y"]; name ["rSFlipFlop"; "R"] ]}) ; 
        comment = { annotated_elem = None ; annotation } } );
  ]
						  
let suite = "Parser" >::: test_cases
