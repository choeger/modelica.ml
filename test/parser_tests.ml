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
  fun _ ->
    try
      f (parser next last)
    with 
      SyntaxError e -> assert_failure (Printf.sprintf "Syntax Error at %s:\n%s" (show_location e) (error_message e input))

let expr_test input f =
  parse_test expr_parser

let parser_test_case parser lprinter sprinter prep input expected =
  (Printf.sprintf "Parse '%s'" input) >::: [
    ("parsing" >::
     parse_test parser input (fun e -> assert_equal ~msg:"equality of parser result" ~printer:sprinter expected (prep e) ) ) ;
    ("re-parsing" >::
     parse_test parser input
       (fun firstpass -> parse_test parser (lprinter firstpass)
           (fun e -> assert_equal ~msg:"equality of re-parsed result" ~printer:sprinter (prep firstpass) (prep e)) ())) ; 
  ]

let erase_location = { identity_mapper with map_loc_t = (fun _ _ -> Location.none) ;
                                            dispatch_component_reference =
                                              {identity_mapper.dispatch_component_reference with
                                               map_RootRef = (fun s kcs -> RootRef (DQ.map (s.map_known_component s) kcs)) ;
                                              } ;
                                            map_known_ref = (fun s r -> {r with known_components=DQ.map (s.map_known_component s) r.known_components}) ;
                     }

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

let prep_defs = List.map (erase_location.map_definition erase_location)

let defs input expected = parser_test_case defs_parser (defs2str ~max:100) (defs2str ~max:20) prep_defs input expected

let prep_typedef = erase_location.map_typedef erase_location 

let typedef input expected = parser_test_case td_parser (td2str ~max:100) (td2str ~max:20) prep_typedef input expected

let prep_unit = erase_location.map_unit_ erase_location 

let unit_ input expected = parser_test_case unit_parser (unit2str ~max:100) (unit2str ~max:20) prep_unit input expected

let test_cases = [ 
  expr "1.234" (real(1.234));
  expr "10e2" (real(1000.));
  expr "x" (ide("x")) ;
  expr "new_foo" (ide "new_foo");
  expr "1" (int(1));

  (* TODO: copy/move to lexer test suite as approporiate *)
  expr "derfoo" (ide "derfoo") ;
  expr "not1" (ide "not1") ;
  expr "foo /* comment */ " (ide "foo") ;
  expr "true" (bool true) ;
  expr "false" (bool false) ;

  expr "\"foo\"" (string "foo") ;

  expr "42" (int 42) ;

  expr "42 /* the answer*/" (int 42) ;

  expr ("42 /*" ^ (String.repeat "the answer " 10000) ^ "*/") (int 42) ;

  expr "42 // the answer" (int 42) ;

  expr "42.0" (real 42.) ;

  expr "\"foo \n bar\"" (string "foo \n bar") ;

  expr "\"\\\"\"" (string "\"") ;

  (let x = (String.repeat "ABC" 1000) in
   expr ("\"" ^ x ^ "\"") (string x) );

  expr "x.bar" (name ["x"; "bar"]);

  expr "'foo'" (ide "'foo'") ;

  expr "'foo' " (ide "'foo'") ;

  expr "'foo'//bar" (ide "'foo'") ;

  expr "'foo \\\\n'" (ide "'foo \\\\n'") ;

  expr ":" colon ;
  expr "der" der ;
  expr "initial" initial ;
  expr "end" end_ ;
  expr "assert" assert_ ;

  expr "a.b.c"  (name ["a"; "b"; "c"]) ;
  expr "a.'b'.c"  (name ["a"; "'b'"; "c"]) ;
  expr "a/* comment */.b.c"  (name ["a"; "b"; "c" ]) ;

  expr ".x" ( cre (UnknownRef {root = true; components = [any "x"]})) ;
  expr ".x.y" ( (cre (UnknownRef {root = true; components = [any "x"; any "y"]}))) ;

  (* functions *)
  expr "f()" (app (cr [any "f"]) []);
  expr "f(1.0)" (app (cr [any "f"]) ["", real 1.]) ;
  expr "f(x=1.0)" (app (cr [any "f"]) ["x", (real 1.0)]);
  expr "f(1.0, x=1.0)" (app (cr [any "f"]) ["", real 1.0; "x", (real 1.0)]);
  expr "function x" (explicitclosure (ide "x"));

  (* precedences *)
  expr "1 + 2 * 3" (plus { left = int 1 ; right = mul { left = int 2 ; right = int 3 } });
  expr "2 * 3 + 1" (plus { left = mul { left = int 2 ; right = int 3 } ; right = int 1 });
  expr "(1 + 2) * 3" (mul { left = plus { left = int 1 ; right = int 2 } ; right = int 3 });
  expr "3 * (1 + 2)" (mul { right = plus { left = int 1 ; right = int 2 } ; left = int 3 });
  expr "3 * 2 ^ 4" (mul { left = int 3 ; right = pow { left = int 2 ; right = int 4 } });
  expr "2 ^ 4 * 3" (mul { right = int 3 ; left = pow { left = int 2 ; right = int 4 } });
  expr "-2 * 3" (uminus (mul { left = int 2 ; right = int 3 }) ) ;
  expr "-2 - 3" (minus { left = uminus (int 2) ; right = int 3 }) ;

  expr "-2 * 3 < 2*3" (lt {left= uminus (mul { left = int 2 ; right = int 3 }) ; right=mul { left = int 2 ; right = int 3 } } ) ;
  expr "-2 * 3 > 2*3" (gt {left= uminus (mul { left = int 2 ; right = int 3 }) ; right=mul { left = int 2 ; right = int 3 } } ) ;
  expr "-2 * 3 <= 2*3" (leq {left= uminus (mul { left = int 2 ; right = int 3 }) ; right=mul { left = int 2 ; right = int 3 } } ) ;
  expr "-2 * 3 >= 2*3" (geq {left= uminus (mul { left = int 2 ; right = int 3 }) ; right=mul { left = int 2 ; right = int 3 } } ) ;
  expr "-2 * 3 <> 2*3" (neq {left= uminus (mul { left = int 2 ; right = int 3 }) ; right=mul { left = int 2 ; right = int 3 } } ) ;
  expr "-2 * 3 == 2*3" (eq_ {left= uminus (mul { left = int 2 ; right = int 3 }) ; right=mul { left = int 2 ; right = int 3 } } ) ;

  expr "1 < 2 and 2 < 3" (and_ {left= (lt { left = int 1 ; right = int 2 }) ; right=lt { left = int 2 ; right = int 3 } }) ;
  expr "1 < 2 or 2 < 3" (or_ {left= (lt { left = int 1 ; right = int 2 }) ; right=lt { left = int 2 ; right = int 3 } }) ;
  expr "1 < 2 and x or y" (or_ {left=and_ {left= (lt { left = int 1 ; right = int 2 }) ; right=ide "x" }; right=ide "y"}) ;

  (* arrays *)
  expr "x[1]" ( (ComponentReference (cr [{(any "x") with subscripts = [int 1]}]))) ;
  expr "x[1].y" ( (ComponentReference (cr [{(any "x") with subscripts = [int 1]}; any "y"]))) ;
  expr "{true}" (array [bool true]);
  expr "[4,2;0,0]" (marray [[int 4; int 2];[int 0; int 0]]);

  (* if/then *)
  expr "if true then false else true" (if_ { condition = bool true; then_ = bool false; else_if = []; else_ = bool true });
  expr "if true then false elseif false then true else true" (if_ { condition = bool true; then_ = bool false;
                                                                    else_if = [{guard=bool false; elsethen=bool true}];
                                                                    else_ = bool true });


  (* comprehension *)
  expr "{x for x in foo}" (array[compr {exp = ide "x"; idxs = [{variable=nl "x"; range=Some (ide "foo")}]}]);
  expr "{x for x}" (array [compr {exp = ide "x"; idxs = [{variable=nl "x"; range=None}]}]);

  (* statements *)
  stmt "return;" (uncommented Return) ;
  stmt "break;" (uncommented Break) ;
  stmt "assert();" (uncommented (Call {procedure=Assert; pargs=[]; pnamed_args = [] }));
  stmt "print(\"... testAllFunctions(..) is logged in \" + file);"
    (uncommented (Call {procedure=cr [any "print"] ; pargs = [
         plus { left=string "... testAllFunctions(..) is logged in "; right = ide "file" }
       ]; pnamed_args =  [] }));

  stmt "if true then break; end if;" (uncommented (IfStmt { condition = bool true ; then_ = [uncommented Break] ; else_if = [] ; else_ = [] }));
  stmt "if true then break; elseif true then break; end if;" (uncommented (IfStmt { condition = bool true ; then_ = [uncommented Break] ; else_if = [{guard=bool true; elsethen=[uncommented Break]}] ; else_ = [] }));
  stmt "when true then break; elsewhen true then break; end when;" (uncommented (WhenStmt { condition = bool true ; then_ = [uncommented Break] ; else_if = [{guard=bool true; elsethen=[uncommented Break]}] ; else_ = [] }));
  stmt "f(1, x=3);" (uncommented (Call { procedure=cr [any "f"]; pargs = [int 1]; pnamed_args = [named "x" (int 3)]} ) );
  stmt "x := 23;" (uncommented (Assignment { target=Single (cr [any "x"]) ; source = int 23 } ));
  stmt "(,) := 23;" (uncommented (Assignment { target=Multiple [None; None] ; source = int 23 } ));
  stmt "() := 23;" (uncommented (Assignment { target=Multiple [None] ; source = int 23 } ));  
  stmt "(x,,y) := 23;" (uncommented (Assignment { target=Multiple ([Some (ide "x");None;Some (ide "y")]) ; source = int 23 } ));  
  stmt "while true loop break; break; end while;" (uncommented (WhileStmt { while_ = bool true ; while_body = [uncommented Break; uncommented Break] ; } ) );
  stmt "for x loop break; break; end for;" (uncommented (ForStmt { idx = [{variable = nl "x"; range=None}] ; body = [uncommented Break; uncommented Break] ; } ) );
  stmt "for x in a loop break; break; end for;" (uncommented (ForStmt { idx = [{variable = nl "x"; range=Some (ide "a")}] ; body = [uncommented Break; uncommented Break] ; } ) );

  (* equations *)
  eq "x = 0;" (uncommented (SimpleEquation { left = ide "x"; right = int 0 })) ;

  eq "if true then x.y = 0; end if;" (uncommented (IfEquation { condition= bool true; then_ = [uncommented (SimpleEquation { left = name ["x";"y"] ;
                                                                                                                             right = int 0 } )] ;
                                                                else_if = []; else_ = [];
                                                              })) ;

  eq "if c(a[i]) then a[i].p.r = {0,0,0}; end if;"  (uncommented (IfEquation {
      condition=app (cr [any "c"])
          ["", cre (cr [{(any "a") with subscripts = [ide "i"]}])] ;
      then_ = [
        uncommented (
          SimpleEquation {
            left = cre (cr [{(any "a")
                             with subscripts = [ide"i"] } ;
                            any "p"; any "r"]) ;
            right = array [int 0; int 0; int 0];
          } ) ] ;
      else_if = []; else_ = [];
    })) ;

  eq "for i loop if true then x = 0; end if; end for;" (uncommented (ForEquation { idx= [{variable=nl "i" ; range=None}];
                                                                                   body=[uncommented (
                                                                                       IfEquation {
                                                                                         condition= bool true;
                                                                                         then_ = [uncommented (SimpleEquation { left = ide "x" ;
                                                                                                                                right = int 0 })];
                                                                                         else_if = []; else_ = []

                                                                                       })] }));
  eq "x = 23;" (uncommented (SimpleEquation { left=ide "x" ; right = int 23 } ));
  eq "(,) = 23;" (uncommented (SimpleEquation { left=outputexpression [None; None] ; right = int 23 } ));
  eq "() = 23;" (uncommented (SimpleEquation { left=outputexpression [None] ; right = int 23 } ));  
  eq "(x,,y) = 23;" (uncommented (SimpleEquation { left=outputexpression([Some (ide "x");None;Some (ide "y")]) ; right = int 23 } ));  


  texpr "Modelica" (type_name ["Modelica"]);
  texpr "Modelica.Icons" (type_name ["Modelica";"Icons"]);
  texpr ".x" (root_type ["x"]);
  texpr ".x.y" (root_type ["x";"y"]);
  texpr "Modelica.Icons.interfacesPackage" (type_name ["Modelica";"Icons";"interfacesPackage"]);
  texpr "input Real" (TCau {flag = Flags.Input ; flagged = type_name ["Real"] });
  texpr "constant Real" (TVar {flag = Flags.Constant ; flagged = type_name ["Real"] });
  texpr "flow Real" (TCon {flag = Flags.Flow ; flagged = type_name ["Real"] });
  texpr "output parameter discrete stream Real" (TCau { flag = Flags.Output ; flagged = TVar { flag = Flags.Parameter ;
                                                                                               flagged =
                                                                                                 TVar { flag = Flags.Discrete ;
                                                                                                        flagged =
                                                                                                          TCon { flag = Flags.Stream ;
                                                                                                                 flagged = type_name ["Real"] } } } } ) ;
  texpr "Real[2,3]" (TArray {base_type = type_name ["Real"]; dims = [int 2 ; int 3]} ) ;
  texpr "T()" (TMod { mod_type = type_name ["T"] ; modification = no_modification } ) ;


  import "import X" (uncommented (Unnamed [nl "X"])) ;
  import "import Y=X" (uncommented (NamedImport {global = [nl "X"] ; local = nl "Y" }));
  import "import Y=.X" (uncommented (NamedImport {global = [nl "X"] ; local = nl "Y" }));

  import "import X.*" (uncommented (UnqualifiedImport [nl "X"]));


  (let extend_statement = { ext_type = (type_name ["Modelica";"Icons";"InterfacesPackage"]) ;
                            ext_annotation = None }
   in
   extend "extends Modelica.Icons.InterfacesPackage" extend_statement );

  defs "Real p" [uncommented {empty_def with def_name = "p" ; def_type = type_name ["Real"] ;}] ;
  defs "Real p(foo={42})" [uncommented {empty_def with def_name = "p" ;
                                                       def_type = TMod{mod_type=type_name ["Real"];
                                                                       modification={no_modification with
                                                                                     modifications=[{comment=no_comment;
                                                                                                     commented={mod_each=false;
                                                                                                                mod_final=false;
                                                                                                                mod_name = [nl "foo"];
                                                                                                                mod_value=Some(Rebind (Array [Int 42]))}
                                                                                                    }]
                                                                                    }} ;}] ;
  
  defs "Real p, q" [uncommented {empty_def with def_name = "p" ; def_type = type_name ["Real"] ;} ;
                    uncommented {empty_def with def_name = "q" ; def_type = type_name ["Real"] ;}
                   ] ;  


  defs "parameter FluidHeatFlow.Media.Medium medium" [uncommented { empty_def with def_name = "medium" ;
                                                                                   def_type = TVar { flag = Flags.Parameter ;
                                                                                                     flagged =
                                                                                                       type_name ["FluidHeatFlow";
                                                                                                                  "Media";
                                                                                                                  "Medium"];
                                                                                                   }
                                                                  }];

  defs "Medium medium := Medium()" [uncommented { empty_def with def_name = "medium" ;
                                                                 def_type = type_name ["Medium"] ;
                                                                 def_rhs = Some ( app (cr [any "Medium"]) [] ) ;
                                                }] ;


  defs "replaceable T t constrainedby S" [uncommented { empty_def with def_name = "t" ;
                                                                       def_type = type_name ["T"] ;
                                                                       def_constraint = Some (uncommented ( type_name ["S"])) ;
                                                                       def_options = { no_def_options with replaceable = true } ;
                                                      }] ;


  defs "Density rho=1.225 \"Air Density\"" [{ commented = { empty_def with def_name = "rho";
                                                                           def_type = type_name ["Density"];
                                                                           def_rhs = Some (real 1.225) ;
                                                          } ;
                                              comment = unannotated ( Some (nl "Air Density")  )}];


  defs "Real friction_pos[:, 2]=[0; 1] \"[w,tau] positive sliding friction characteristic (w>=0)\""
    [{ commented = { empty_def with def_name = "friction_pos";
                                    def_type = TArray { base_type=type_name ["Real"]; dims = [colon ; int 2] } ;
                                    def_rhs = Some (marray [[int 0];[int 1]]) ;
                   } ;
       comment = unannotated ( Some (nl "[w,tau] positive sliding friction characteristic (w>=0)") ) 
     }];

  typedef "type T = A" (uncommented (Short { empty_typedef with td_name = nl "T" ; type_exp = type_name ["A"] })) ;

  (let def = uncommented { empty_def with def_name = "x" ; def_type = type_name ["S"] } in
   typedef "class T S x; end T" (uncommented (Composition { empty_typedef with td_name = nl"T" ;
                                                                               type_exp = {empty_composition with public = {
                                                                                   empty_elements with
                                                                                   defs = [def] } };
                                                                               sort = Flags.Class ;
                                                          } )));

  (let def = uncommented { empty_def with def_name = "x" ; def_type = type_name ["S"] } in
   typedef "class T \"comment\" S x; end T" { commented = Composition { empty_typedef with td_name = nl"T" ;
                                                                                           type_exp = {
                                                                                             empty_composition with
                                                                                             public = { empty_elements with
                                                                                                        defs = [def] }};
                                                                                           sort = Flags.Class ;
                                                                      } ;
                                              comment = unannotated ( Some (nl "comment") ) ;
                                            } );

  typedef "record A end A" (uncommented (Composition {empty_typedef with td_name =nl"A" ; sort=Flags.Record; type_exp = empty_composition})) ;
  
  typedef "partial model A end A" (uncommented (Composition { empty_typedef with td_name = nl"A" ;
                                                                                 type_exp = empty_composition;
                                                                                 sort = Flags.Model ;
                                                                                 type_options = { no_type_options with partial = true };
                                                            } ));

  typedef "replaceable model A end A" (uncommented (Composition { empty_typedef with td_name = nl"A" ;
                                                                                     type_exp = empty_composition;
                                                                                     sort = Flags.Model ;
                                                                                     type_options = {
                                                                                       no_type_options with type_replaceable = true };
                                                                } ));

  typedef "replaceable package A end A" (uncommented (Composition { empty_typedef with td_name = nl"A" ;
                                                                                       type_exp = empty_composition;
                                                                                       sort = Flags.Package ;
                                                                                       type_options = {
                                                                                         no_type_options with type_replaceable = true };
                                                                  } ));


  typedef "encapsulated model A end A" (uncommented (Composition { empty_typedef with td_name = nl"A" ;
                                                                                      type_exp = empty_composition;
                                                                                      sort = Flags.Model ;
                                                                                      type_options = {
                                                                                        no_type_options with encapsulated = true };
                                                                 } ));

  typedef "replaceable encapsulated partial model A end A"
    (uncommented (Composition { empty_typedef with td_name = nl"A" ;
                                                   type_exp = empty_composition;
                                                   sort = Flags.Model ;
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
                                                                           redeclared_typedefs = [
                                                                             uncommented (
                                                                               Short { empty_typedef with td_name = nl"T" ;
                                                                                                          type_exp = type_name ["S"]
                                                                                     }
                                                                             )] } 
                                                              } ;
                                                   sort = Flags.Model ;
                              } ));

  typedef "model X replaceable package T = S; end X"
    (uncommented (Composition { empty_typedef with td_name = nl"X" ;
                                                   type_exp = { empty_composition with
                                                                public = { empty_elements with
                                                                           typedefs = [ uncommented (
                                                                               Short { empty_typedef with td_name = nl"T" ;
                                                                                                          type_exp = type_name ["S"] ;
                                                                                                          sort = Flags.Package ;
                                                                                                          type_options = {
                                                                                                            no_type_options with
                                                                                                            type_replaceable =
                                                                                                              true
                                                                                                          }
                                                                                     })]} ;
                                                              } ;
                                                   sort = Flags.Model ;
                              } ));

  typedef "model X equation 1 = 1; end X"
    (uncommented (Composition { empty_typedef with td_name = nl"X" ;
                                                   type_exp = { empty_composition with
                                                                cargo = { empty_behavior with
                                                                          equations = [ uncommented (
                                                                              SimpleEquation {
                                                                                left=int 1;
                                                                                right=int 1}
                                                                            )]
                                                                        } ;
                                                              } ;
                                                   sort = Flags.Model ;
                              } ));

  typedef "model X annotation ();  end X"
    ({commented = (Composition { empty_typedef with td_name = nl"X" ;
                                                    type_exp = empty_composition ;
                                                    sort = Flags.Model ;
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
                                                sort = Flags.Class ;
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
                                                         ext_call=Some {                                                                                  ext_lhs=None;
                                                                                                                                                          ext_ident = "f";
                                                                                                                                                          ext_args = [] }
                                                       }
                                                     )
                                                 } ;
                                       } ;
                            sort = Flags.Function } ));

  typedef "function f external \"C\" x = f(); end f"
    (uncommented (Composition { empty_typedef with td_name = nl"f" ;
                                                   type_exp = { empty_composition with
                                                                cargo = { empty_behavior with
                                                                          external_ = Some (
                                                                              unannotated {
                                                                                lang="C" ;
                                                                                ext_call=Some{                                                                                  ext_lhs=Some (cr [any "x"]);
                                                                                                                                                                                ext_ident = "f";
                                                                                                                                                                                ext_args = [] }
                                                                              }
                                                                            )
                                                                        } ;
                                                              } ;
                                                   sort = Flags.Function } ));

  typedef "type A = B(redeclare type C = D)"
    (uncommented (Short { empty_typedef with
                          td_name = nl"A" ;
                          type_exp = TMod { mod_type=type_name ["B"] ;
                                            modification = { no_modification with
                                                             redeclared_types = [{ redecl_each = false ;
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
                                              redeclared_types = [{ redecl_each = false ;
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
                                                             redeclared_components = [{ each = false ;
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
                                                             redeclared_components = [{ each = false ;
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
                                                                    Call {procedure=cr [any "print"] ;
                                                                          pargs = [string "hello, world!"] ;
                                                                          pnamed_args = [] } ) ]];
                                                              } ;
                                                    } ;
                                         sort = Flags.Function } ));

  unit_ "package Test end Test;" {within = None; toplevel_defs = [(uncommented (Composition {empty_typedef with td_name =nl"Test" ;
                                                                                                                sort=Flags.Package;
                                                                                                                type_exp = empty_composition}))]} ;

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
                                                                       array [
                                                                         array [uminus (int 19); uminus (int 10)];
                                                                         array [int 20;uminus (int 10)];
                                                                         array [int 20;uminus (int 6)];
                                                                         array [int 38;uminus (int 6)];
                                                                       ]));
                                                                  };
                                                      uncommented {mod_each=false;mod_final=false;
                                                                   mod_name=[nl "color"];
                                                                   mod_value=Some (Rebind (array [int 255;int 0;int 255]));
                                                                  }                                                                
                                                     ]})
                          }]}
   in
   let annotation = Some line in
   eq "connect(not1.y, rSFlipFlop.R) annotation (Line(points={{-19,-10},{20,-10}, {20,-6},{38,-6}}, color={255,0,255}));" 
     { commented = Connect {connlhs = unknownref ["not1";"y"]; connrhs = unknownref ["rSFlipFlop"; "R"]} ; 
       comment = { annotated_elem = None ; annotation } } );
]

let suite = "Parser" >::: test_cases
