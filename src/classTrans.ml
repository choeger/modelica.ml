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


(** Translation of Modelica type/class-expressions to classLang *)

open Ast.Flags
open Syntax
open Utils
open Location
open Motypes
open Batteries
open ClassDeps
       
exception UnqualifiedImportNotSupported
exception NothingModified
exception InconsistentHierarchy
            
type import_env = DS.name StrMap.t
            
let add_import env import = match import.commented with
    | NamedImport {global=[]; _} | Unnamed [] -> (* cannot happen, make ocamlc happy *) env                                                                    
    (* in the case of a renaming import, pick up the substitution *)
    | NamedImport {global;local} ->
       BatLog.logf "Importing %s = %s\n" local.txt (show_name global);
       StrMap.add local.txt global env

    | Unnamed name -> begin match List.rev name with
                              [] -> raise (Failure "Cannot happen.") (* really, see pattern above *)
                            | local::global -> StrMap.add local.txt name env
                      end
                        
    | UnqualifiedImport name -> raise UnqualifiedImportNotSupported

				      
let sort sort arg = if sort = Class then arg else Constr {arg; constr = CSort sort}
                                      
let repl opts arg = match opts with {type_replaceable=true} -> Constr {arg; constr = CRepl}
                                  | _ -> arg

let final opts arg = match opts with {type_final=false} -> Constr {arg; constr=CRepl}
                                   | _ -> arg
					    
type translation_state = {
    env : import_env ;
    current_path : class_ptr ;
    anons : int ;
    code : class_stmt list ;
  }
			   
let rec add_imports imports state = match imports with
    [] -> ((),state)
  | i::imports -> add_imports imports {state with env = add_import state.env i}
			   
let return x = fun s -> (x, s)

let bind ma f = fun s -> let (a, s') = ma s in
			 (f a s') 

let run m = let (a,s) = m {env = StrMap.empty ; current_path = DQ.empty ; anons = 0; code = []} in a

let down pe state = ((), {state with current_path = DQ.snoc state.current_path pe})

let within_path = function 
    None -> return ()
  | Some (ps) -> fun state -> ((), {state with current_path = DQ.of_list (List.map (fun str -> `ClassMember str.txt) ps)})
		      		      
let up state = ((), {state with current_path = match DQ.rear state.current_path with None -> DQ.empty | Some (xs,_) -> xs})
		 
let define rhs state = ((), {state with code = {lhs=state.current_path; rhs} :: state.code})

let open_class sort post state = ((), {state with code =
						    {lhs = state.current_path ;
						     rhs = Close } ::
						    {lhs = state.current_path;
						     rhs = (post (Empty {class_sort = sort; class_name = (Name.of_ptr state.current_path)}))} :: state.code})

let in_context m state =
  let (x, s') = m {state with anons = (Hashtbl.hash state.current_path)} in
  (x, {state with code = s'.code})

let inside name m state =
  let (x, s') = m {state with current_path = name} in
  (x, {s' with current_path = state.current_path})

let current_path state = (state.current_path, state)
    
let in_superclass state = match DQ.rear state.current_path with
    Some(xs, `SuperClass _) -> (true, state)
  | _ -> (false, state)
    
let rec mseqi_ i fm list state = match list with
    [] -> ((), state)
  | x::xs -> let (a', s) = fm i x state in
	     mseqi_ (i+1) fm xs s

let mseqi = mseqi_ 0
		   
let rec mseq fm list state = match list with
    [] -> ((), state)
  | x::xs -> let (_, s) = fm x state in
	     mseq fm xs s

let rec mfold a f fm list state = match list with
    [] -> (a, state)
  | x::xs -> let (a', s) = fm x state in
	     mfold (f a a') f fm xs s

let apply_import n state = match n with
    | x::xs when StrMap.mem x.txt state.env -> ((StrMap.find x.txt state.env) @ xs, state)
    | xs -> (xs, state)

let get state = (state, state)

let set state s = ((), state)

let set_env env state = ((), {state with env})
		    
let next_anon state = `ClassMember ("anon" ^ (string_of_int state.anons)), {state with anons = state.anons + 1}
   			    
let rec mtranslate_tds = function
  | Short tds -> do_ ;
		 (* new path is the definition *)
		 down (`ClassMember tds.td_name.txt) ;
		 (* Translate the rhs of the type-definition *)
		 te <-- mtranslate_texp ((sort tds.sort) %> (repl tds.type_options)) tds.type_exp ;
		 (* restore path *)
		 up ;
		 return ()

  | Composition tds ->
     do_ ;
     in_context (
	 do_ ;
	 add_imports tds.type_exp.imports ;
	 (* Class name *)
	 down (`ClassMember tds.td_name.txt) ;
	 (* Class skeleton *)
	 open_class tds.sort (repl tds.type_options) ;
	 (* Public elements *)
	 mtranslate_elements tds.type_exp.public ;	 
	 (* Protected elements *)
	 down `Protected ;
	 mtranslate_elements tds.type_exp.protected 
       )     

  | Enumeration tds ->
     do_ ;
     down (`ClassMember tds.td_name.txt) ;
     define (repl tds.type_options (sort tds.sort (PEnumeration (StrSet.of_list (List.map (fun {commented} -> commented) tds.type_exp))))) ;
     up
       
  | OpenEnumeration tds ->
     do_ ;
     down (`ClassMember tds.td_name.txt) ;
     define (repl tds.type_options (sort tds.sort (PEnumeration StrSet.empty))) ;
     up
                          
  | DerSpec tds ->
     do_ ;
     down (`ClassMember tds.td_name.txt) ;
     define (repl tds.type_options (sort tds.sort (Constr {arg = Reference tds.type_exp.der_name ; constr = CDer (lunloc tds.type_exp.idents)}))) ;
     up 

  | Extension tds ->
     let (cmp, _) = tds.type_exp in
     in_context (
	 do_ ;
	 add_imports cmp.imports ;
	 down (`ClassMember tds.td_name.txt) ;
	 open_class tds.sort (repl tds.type_options) ;
	 mtranslate_elements cmp.public ;
	 down (`SuperClass (List.length cmp.public.extensions)) ;
	 define RedeclareExtends ; up ;
	 down `Protected ;
	 mtranslate_elements cmp.protected
       )
		
and mtranslate_texp post =
  let appl ct constr = let f' = fun arg -> post (Constr {arg;constr}) in
                       mtranslate_texp f' ct
  in
  function
  | TName [{txt="ExternalObject"}] -> define (post PExternalObject)
  | TName [{txt="StateSelect"}] -> define (post (PEnumeration (StrSet.of_list ["never";"default";"avoid";"prefer";"always"])))
  | TName [{txt="Real"}] -> define (post PReal)
  | TName [{txt="Integer"}] -> define (post PInt)
  | TName [{txt="Boolean"}] -> define (post PBool)
  | TName [{txt="String"}] -> define (post PString)

  | TName n -> do_ ; r <-- apply_import n ;
	       define (post (Reference r))
  | TRootName n -> define (post (RootReference n))
                                 
  | TArray {base_type;dims} -> appl base_type (CArray (List.length dims))
  | TVar {flag;flagged} -> appl flagged (CVar flag)                                
  | TCon {flag;flagged} -> appl flagged (CCon flag)
  | TCau {flag;flagged} -> appl flagged (CCau flag)

  | TMod {mod_type; modification} ->
     do_ ;
     state <-- get ;
     let s = state.current_path in
     let src = match DQ.rear s with None -> raise InconsistentHierarchy | Some(xs,_) -> xs in
     a <-- next_anon ;
     let pullout = DQ.snoc src a in     
     define (KnownPtr pullout) ;
     up ;
     down a ;
     open_class Class (fun x -> x) ;
     down (`SuperClass 0) ;
     mtranslate_texp (fun x -> x) mod_type ;
     up ;     
     redec <-- mtranslate_modification src modification ;

     (* Do not introduce a new class in case of (nested) modifications without redeclarations *)
     if (not redec) then begin
         do_ ;
         set state ;
         mtranslate_texp (fun x -> x) mod_type 
       end
     else
       return ()
       
and mtranslate_extends i {ext_type} =
  do_ ;
  down (`SuperClass i) ;
  mtranslate_texp identity ext_type ;
  up 
		  
and mtranslate_elements {extensions;typedefs;redeclared_types;defs;redeclared_defs} = 
  do_ ;
  mseqi mtranslate_extends extensions ;
  mseq mtranslate_typedef typedefs ;
  mseq mtranslate_def defs ;
  mseq mtranslate_typedef redeclared_types ;
  mseq mtranslate_def redeclared_defs

and mtranslate_typedef td = mtranslate_tds td.commented

and mtranslate_def def =
  do_ ;
  down (`FieldType def.commented.def_name) ;
  mtranslate_texp (repl {Syntax_fragments.no_type_options with type_replaceable = def.commented.def_options.replaceable}) def.commented.def_type ;
  up

and mtranslate_type_redeclaration src {redecl_type} =
  let tds = redecl_type.commented in
  (* a redeclared type is resolved in the parent class scope *)
  do_ ;
  a <-- next_anon ;
  let pullout = DQ.snoc src a in
  inside pullout (mtranslate_texp (final tds.type_options %> sort tds.sort) tds.type_exp ) ;
  down (`ClassMember tds.td_name.txt) ;  
  define (KnownPtr pullout) ;  
  up 
                            
and mtranslate_modification src {types; components; modifications} =
  do_ ;
  mseq (mtranslate_type_redeclaration src) types ;
  mseq (mtranslate_def_redeclaration src) components ; 
  x <-- mfold false (||) (mtranslate_nested_modification src) modifications ;
  return (x || types != [] || components != [])
                 
and mtranslate_nested_modification src = function
    {commented = {mod_name =  []; mod_value = Some (Nested nested | NestedRebind {nested}) }} ->    
    mtranslate_modification src nested
  | {commented = {mod_name =  x::xs; mod_value = Some (Nested nested | NestedRebind {nested}) }} ->
     down (`Any x.txt) ;
     open_class Class (fun x -> x) ;
     down (`SuperClass 0) ;
     define RedeclareExtends ;
     up;
     mtranslate_modification src nested
  | _ -> return false                                              

and mtranslate_def_redeclaration src {def} = do_ ;
					     (* a redeclared type is resolved in the parent class scope *)
					     f <-- next_anon ;
					     let pullout = DQ.snoc src f in
					     inside pullout (mtranslate_texp (repl {Syntax_fragments.no_type_options with type_replaceable = def.commented.def_options.replaceable}) def.commented.def_type) ;
					     down (`FieldType def.commented.def_name) ;
					     define (KnownPtr pullout) ;  
					     up
						    
(*    
let rec translate_tds fresh env p (prog : class_stmt list) = function
  | Short tds ->
     let p' = DQ.snoc p (`ClassMember tds.td_name.txt) in
     translate_texp env p' prog ((sort tds.sort) %> (repl tds.type_options)) tds.type_exp

  | Composition tds ->
     let env' = (List.fold_left add_import env tds.type_exp.imports) in
     let p' = DQ.snoc p (`ClassMember tds.td_name.txt) in
     let rhs = repl tds.type_options (Empty {class_sort = tds.sort; class_name = (Name.of_ptr p')}) in
     let prog' = {lhs=p'; rhs=Close}::{lhs=p'; rhs}::prog in
     let public = translate_elements env' p' prog' tds.type_exp.public in
     let p'' = (DQ.snoc p' `Protected) in
     let protected = translate_elements env' p'' public tds.type_exp.protected in
     protected

  | Enumeration tds ->
     let p' = DQ.snoc p (`ClassMember tds.td_name.txt) in
     let rhs = repl tds.type_options (sort tds.sort (PEnumeration (StrSet.of_list (List.map (fun {commented} -> commented) tds.type_exp)))) in
     {lhs=p'; rhs}::prog

  | OpenEnumeration tds ->
     let p' = DQ.snoc p (`ClassMember tds.td_name.txt) in
     let rhs = repl tds.type_options (sort tds.sort (PEnumeration StrSet.empty)) in
     {lhs=p'; rhs}::prog
                          
  | DerSpec tds ->
     let p' = DQ.snoc p (`ClassMember tds.td_name.txt) in
     let rhs = repl tds.type_options (sort tds.sort (Constr {arg = Reference tds.type_exp.der_name ; constr = CDer (lunloc tds.type_exp.idents)})) in
     {lhs=p'; rhs}::prog

  | Extension tds ->
     let (cmp, _) = tds.type_exp in
     let env' = (List.fold_left add_import env cmp.imports) in
     let p' = DQ.snoc p (`ClassMember tds.td_name.txt) in
     let rhs = repl tds.type_options (Empty {class_name = Name.of_ptr p'; class_sort = tds.sort}) in
     let prog' = {lhs=p'; rhs=Close}::{lhs=p'; rhs}::prog in
     let public = translate_elements env' p' prog' cmp.public in

     let baseclass = 
       {lhs=DQ.snoc p' (`SuperClass (List.length cmp.public.extensions)); rhs=RedeclareExtends}::public                                                                                                  
     in
     let p'' = (DQ.snoc p' `Protected) in
     let protected = translate_elements env' p'' baseclass cmp.protected in
     protected

                      
and translate_extends fresh env p (prog : class_stmt list) i {ext_type} =  
  translate_texp env (DQ.snoc p (`SuperClass i)) prog identity ext_type

and translate_elements fresh env p prog {extensions;typedefs;redeclared_types;defs;redeclared_defs} = 
  let super = List.fold_lefti (translate_extends env p) prog extensions in
  let class_members = List.fold_left (translate_typedef env p) super typedefs in
  let fields = List.fold_left (translate_def env p) class_members defs in  
  let type_redecls = List.fold_left (translate_typedef env p) fields redeclared_types in    
  let field_redecls = List.fold_left (translate_def env p) type_redecls redeclared_defs in  
  field_redecls  

and translate_typedef fresh env p prog td = translate_tds env p prog td.commented
                                                  
and translate_def fresh env p prog def = translate_texp env (DQ.snoc p (`Field def.commented.def_name)) prog
							(repl {Syntax_fragments.no_type_options with type_replaceable = def.commented.def_options.replaceable})
                                                  def.commented.def_type 
                                                    
(*
-and translate_strict_redeclarations rd_lhs {types} =
-  StrictRedeclaration {rd_lhs ; rds = List.map (fun trd -> let rd_name = trd.redecl_type.commented.td_name.txt in
-                                                           let rd_rhs  = translate_texp trd.redecl_type.commented.type_exp
-                                                           in ClassMember {rd_name ; rd_rhs}) types}
                                                    *)
                                                  
and translate_texp env p (prog : class_stmt list) f =
  let appl ct constr = let f' = fun arg -> f(Constr {arg;constr}) in
                       translate_texp env p prog f' ct
  in
  let return t = {lhs=p; rhs= f t}::prog in
  let apply_import = function
    | x::xs when StrMap.mem x.txt env -> (StrMap.find x.txt env) @ xs
    | xs -> xs
  in
  function
  | TName [{txt="ExternalObject"}] -> return PExternalObject
  | TName [{txt="StateSelect"}] -> return (PEnumeration (StrSet.of_list ["never";"default";"avoid";"prefer";"always"]))
  | TName [{txt="Real"}] -> return PReal
  | TName [{txt="Integer"}] -> return PInt
  | TName [{txt="Boolean"}] -> return PBool
  | TName [{txt="String"}] -> return PString
  | TName n -> return (Reference (apply_import n))
  | TRootName n -> return (RootReference n)
                                 
  | TArray {base_type;dims} -> appl base_type (CArray (List.length dims))
  | TVar {flag;flagged} -> appl flagged (CVar flag)                                 
  | TCon {flag;flagged} -> appl flagged (CCon flag)
  | TCau {flag;flagged} -> appl flagged (CCau flag)

  | TMod {mod_type; modification} ->
     (* order does not matter here: will be found by dependency analysis *)
     begin match DQ.rear p with
             None -> raise NothingModified (* cannot happen *)
           (* In case of inheritance, we do not need to handle redeclarations special from normal declarations *)
           | Some(parent, `SuperClass _) ->
              let prog' = translate_modification env parent prog modification in
              translate_texp env p prog' f mod_type
           (* This is a little bit wonky: Actually there should be a fresh class name generated here ... *)
           | _ ->	      
              let prog' = translate_modification env p prog modification in
              if (prog == prog') then
                translate_texp env p prog f mod_type
              else
                translate_texp env (DQ.snoc p (`SuperClass 0)) ({lhs=p; rhs=Close}::{lhs=p; rhs=Empty {class_sort=Class;class_name=Name.of_ptr p}}::prog') f mod_type
       end

and translate_type_redeclaration env p prog {redecl_type} =
  let tds = redecl_type.commented in
  let p' = DQ.snoc p (`ClassMember tds.td_name.txt) in
  translate_texp env p' prog (final tds.type_options %> sort tds.sort) tds.type_exp
                            
and translate_modification env p prog {types; components; modifications} =
  let rts = List.fold_left (translate_type_redeclaration env p) prog types in
  let rds = List.fold_left (translate_def_redeclaration env p) rts components in
  List.fold_left (translate_nested_modification env p) rds modifications
  
and translate_nested_modification env p prog = function
    {commented = {mod_name; mod_value = Some (Nested nested | NestedRebind {nested}) }} ->
    let p' = List.fold_left (fun p n -> DQ.snoc p (`Any n.txt)) p mod_name in
    translate_modification env p' prog nested
  | _ -> prog                                                                           

and translate_def_redeclaration env p prog {def} = translate_def env p prog def
           
let rec translate_typedefs env p (prog : class_stmt list) = function
    [] -> prog
  | td::typedefs -> let prog' = translate_tds env p prog td.commented in
                    translate_typedefs env p prog' typedefs
 *)
    							
type translated_unit = {
    class_name : Name.t;
    class_code : class_stmt list;
  } [@@deriving show,yojson]

let name_of = function
  | Short tds -> tds.td_name
  | Composition tds -> tds.td_name
  | Enumeration tds -> tds.td_name
  | OpenEnumeration tds -> tds.td_name
  | DerSpec tds -> tds.td_name
  | Extension tds -> tds.td_name
                         
open FileSystem

let mtranslate_unit env {within; toplevel_defs=td::_} =
  do_ ;
  set_env env ;
  within_path within ;
  mtranslate_typedef td ;
  down (`ClassMember (name_of td.commented).txt) ;
  s <-- get ;
  return {class_code=s.code; class_name=Name.of_ptr s.current_path}
       
let translate_unit env {scanned; parsed} =
  BatLog.logf "[modclc] %s\n" scanned ;
  BatIO.flush (!BatLog.output) ;
  run (mtranslate_unit env parsed)

let rec translate_package env {pkg_name; package_unit; external_units; sub_packages} =  
  (* fetch the imports from the package.mo *)
  let env' = match package_unit.parsed with {toplevel_defs = {commented = Composition tds}::_} -> (List.fold_left add_import env tds.type_exp.imports)
                                          | _ -> env
  in
  let package_unit = translate_unit env' package_unit in
  let external_units = List.map (translate_unit env') external_units in
  let sub_packages = List.map (translate_package env') sub_packages in
  {pkg_name; package_unit; external_units; sub_packages}
  
let translate_pkg_root {root_units; root_packages} =
  let root_units = List.map (translate_unit StrMap.empty) root_units in
  let root_packages = List.map (translate_package StrMap.empty) root_packages in
  {root_units; root_packages}

                                          
  
  
