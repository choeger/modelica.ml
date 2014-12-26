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
 *     names of its contributors may be used to orse or promote products
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

%token GT LT NEQ GEQ LEQ EQ EQEQ LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE SEMICOLON COMMA DOT COLON COLONEQ

%token <int> INT
%token <float> FLOAT
%token <string> IDENT
%token <string> QIDENT                                 
%token <string> STRING
%token DOTPOWER POWER PLUS MINUS TIMES DIV DOTPLUS DOTMINUS DOTTIMES DOTDIV 
%token EOF

%token ALGORITHM DISCRETE FALSE LOOP PURE AND EACH FINAL MODEL RECORD ANNOTATION ELSE
%token FLOW NOT REDECLARE ASSERT ELSEIF FOR OPERATOR REPLACEABLE BLOCK ELSEWHEN FUNCTION OR RETURN
%token BREAK ENCAPSULATED IF OUTER STREAM CLASS END IMPORT OUTPUT THEN CONNECT ENUMERATION IMPURE
%token PACKAGE TRUE CONNECTOR EQUATION IN PARAMETER TYPE CONSTANT EXPANDABLE INITIAL PARTIAL WHEN
%token CONSTRAINEDBY EXTENDS INNER PROTECTED WHILE DER EXTERNAL INPUT PUBLIC WITHIN
%token ENDWHEN ENDIF ENDFOR ENDWHILE

%right lowest /* lowest precedence */
%nonassoc IDENT INT FLOAT STRING LPAREN RPAREN RBRACKET LBRACE RBRACE 

%left COMMA 
%left SEMICOLON 
%left GT LT NEQ GEQ LEQ EQ 
%left PLUS MINUS DOTPLUS DOTMINUS     /* medium precedence */
%right UMinus
%left TIMES DIV DOTTIMES DOTDIV
%left POWER DOTPOWER
%nonassoc below_app
%left app_prec     
%left DOT LBRACKET /* highest precedence */


%{
   open Syntax
   open Utils
%}


%start <Syntax.exp> modelica_expr
%start <Syntax.statement> modelica_stmt
%start <Syntax.equation> modelica_eq
%start <Syntax.texp> modelica_texpr
                                                    
%%

modelica_expr: e = expr EOF { e }

modelica_stmt : s = statement EOF { s }                        

modelica_eq : eq = equation EOF { eq }                              

modelica_texpr : texpr = type_expression EOF { texpr }
                            
optional_expr : e = expr { e }
              | { Empty}                                                  

expr : e = simple_expr { e }
     | IF condition = expr THEN then_ = expr else_if = list(else_if) ELSE else_=expr
       { If { condition ; then_ ; else_if ; else_ } }

simple_expr:
  | TRUE { Bool(true) }
  | FALSE { Bool(false) }
  | i = INT 
        { Int (i) }
  | f = FLOAT
        { Real (f) }
  | s = STRING
        { String(s) }
  | DOT x = IDENT
        { RootIde x}
  | x = IDENT 
        { Ide(x) }
  | x = QIDENT 
        { Ide(x) }
  | LPAREN e = optional_expr RPAREN
        { e }
  | LPAREN hd=optional_expr COMMA tl=separated_nonempty_list(COMMA, optional_expr) RPAREN
        { Tuple (hd::tl) }
  | LBRACE es=array_args RBRACE
        { Array es }
  | lhs = expr LBRACKET indices=separated_nonempty_list(COMMA, expr) RBRACKET
        { ArrayAccess { lhs; indices } }
  | LBRACKET els = separated_nonempty_list(SEMICOLON, separated_nonempty_list(COMMA, expr)) RBRACKET
        { MArray els }
  | FUNCTION e = expr
        { ExplicitClosure e }           
  | END { End } %prec END
  | DER { Der }
  | INITIAL { Initial }
  | COLON { Colon }

  | fun_ = expr LPAREN arguments = function_args RPAREN
        { let (args, named_args) = arguments in App { fun_ ; args; named_args } }
                                                   
  | left = expr PLUS right = expr
       { Plus ( {left ; right} ) } 
  | left = expr MINUS right = expr
       { Minus ( {left ; right} ) } 
  | left = expr TIMES right = expr
       { Mul ( {left ; right} ) } 
  | left = expr DIV right = expr
       { Div ( {left ; right} ) } 
  | left = expr POWER right = expr
       { Pow ( {left ; right} ) } 

       
  | left = expr DOTPLUS right = expr
       { DPlus ( {left ; right} ) } 
  | left = expr DOTMINUS right = expr
       { DMinus ( {left ; right} ) } 
  | left = expr DOTTIMES right = expr
       { DMul ( {left ; right} ) } 
  | left = expr DOTDIV right = expr
       { DDiv ( {left ; right} ) } 
  | left = expr DOTPOWER right = expr
       { DPow ( {left ; right} ) } 

  | object_ = expr DOT field = IDENT
       { Proj { object_ ; field } }
  | object_ = expr DOT field = QIDENT
       { Proj { object_ ; field } }

  | MINUS e = expr { UMinus e } %prec UMinus
  | PLUS e = expr { UPlus e } %prec UMinus
  | DOTMINUS e = expr { UDMinus e } %prec UMinus
  | DOTPLUS e = expr { UDPlus e } %prec UMinus
    
else_if : ELSEIF guard=expr THEN elsethen = expr { {guard; elsethen} }

index_range : IN e = expr { e }
                                                 
index : variable = IDENT range = option(index_range) { { variable ; range } }

array_args : es=separated_list(COMMA, expr) { es }
           | exp = expr FOR idxs = separated_nonempty_list(COMMA, index) { [Compr { exp ; idxs }] }

function_args : e = expr COMMA fs = function_args { let (args, named_args) = fs in (e::args, named_args) }
              | e = expr { ([e], StrMap.empty) }
              | m = named_function_args { ([], m) }
              | exp = expr FOR idxs = separated_nonempty_list(COMMA, index) { ([Compr { exp ; idxs }],StrMap.empty) }  
               
named_argument : x=IDENT EQ e=expr { (x,e) }

named_function_args : args=separated_nonempty_list (COMMA, named_argument) { StrMap.of_enum (List.enum args) }
                    | { StrMap.empty }                                                            

annotation : ANNOTATION LPAREN RPAREN { {types = []; components = []; modifications = []} } 
                        
comment : s=option(STRING) m=option(annotation) { { annotated_elem=s ; annotation=m} }
                        
statement : s=statement_body comment=comment SEMICOLON { {commented=s ; comment} }

else_statements : ELSE else_ = list(statement) { else_ }
                | { [] }

elseif_statement : ELSEIF guard = expr THEN elsethen=list(statement) { { guard ; elsethen } }

elsewhen_statement : ELSEWHEN guard = expr THEN elsethen=list(statement) { { guard ; elsethen } }
                    
component_reference : x = IDENT { Ide x }
                    | DOT x = IDENT { RootIde x }                                                     
                    | object_=component_reference DOT field=IDENT { Proj { object_ ; field } }
                    | lhs = component_reference LBRACKET indices=separated_nonempty_list(COMMA, expr) RBRACKET
                                                                                        { ArrayAccess { lhs; indices } }
lexpr : e=component_reference { e }
      | LPAREN es=separated_list(COMMA, expr) RPAREN { Tuple es }
                      
statement_body : procedure=component_reference LPAREN arguments = function_args RPAREN
                 { let (pargs, pnamed_args) = arguments in Call { procedure ; pargs; pnamed_args } }                                                                 
               | BREAK { Break }
               | RETURN { Return }
               | IF condition=expr THEN then_ = list(statement) else_if = list(elseif_statement) else_ = else_statements ENDIF
                    { IfStmt { condition; then_ ; else_if; else_ } }
               | WHEN condition=expr THEN then_ = list(statement) else_if = list(elsewhen_statement) ENDWHEN
                    { WhenStmt { condition; then_ ; else_if; else_ = []} }                                                                                                                         
               | FOR idx = list(index) LOOP body=list(statement) ENDFOR { ForStmt { idx; body } }
               | WHILE while_=expr LOOP do_ = list(statement) ENDWHILE { WhileStmt { while_; do_ } }
               | target=lexpr COLONEQ source=expr { Assignment { target; source } }                       

                                               
equation : commented=equation_body comment=comment SEMICOLON { { commented ; comment } }

else_equations : ELSE else_ = list(equation) { else_ }
                | { [] }

elseif_equation : ELSEIF guard = expr THEN elsethen=list(equation) { { guard ; elsethen } }

elsewhen_equation : ELSEWHEN guard = expr THEN elsethen=list(equation) { { guard ; elsethen } }

equation_body : e = simple_expr { ExpEquation e }
              | eq_lhs = simple_expr EQ eq_rhs = expr { SimpleEquation { eq_lhs ; eq_rhs } }                                              
              | IF condition=expr THEN then_ = list(equation) else_if = list(elseif_equation) else_ = else_equations ENDIF
                   { IfEquation { condition; then_ ; else_if; else_ } } 
              | WHEN condition=expr THEN then_ = list(equation) else_if = list(elsewhen_equation) ENDWHEN
                   { WhenEquation { condition; then_ ; else_if; else_ = []} }                                                                                                                         
              | FOR idx = list(index) LOOP body=list(equation) ENDFOR { ForEquation { idx; body } }

variability : CONSTANT { Constant }
            | PARAMETER { Parameter } 
            | DISCRETE { Discrete }
                       
connectivity : FLOW { Flow }
             | STREAM { Stream } 

causality : INPUT { Input }                      
          | OUTPUT { Output } 
                  
type_expression : x = IDENT { TIde x }
                | DOT x = IDENT { TRootide x } 
                | class_type=type_expression DOT type_element = IDENT { TProj {class_type; type_element} }
                | flag=variability flagged=type_expression { TVar { flag ; flagged } }
                | flag=causality flagged=type_expression { TCau { flag ; flagged } }
                | flag=connectivity flagged=type_expression { TCon { flag ; flagged } }
                | base_type = type_expression LBRACKET dims = separated_list(COMMA, expr) RBRACKET { TArray { base_type ; dims } }
                            
