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


(** Translation of Modelica units to intermediate representation *)

open Syntax
open Syntax_fragments
open Flags
open Utils
open Location

open Batteries
open Utils
open ModlibInter

exception UnqualifiedImportNotSupported
exception NothingModified
exception InconsistentHierarchy

type import_env = DS.name StrMap.t

let order_defs {defs} = List.mapi
    (fun i d ->
       {fld_name = d.commented.def_name; fld_pos = i;
        fld_defined = d.commented.def_rhs <> None} 
    ) defs

let order_modified_defs m =
  List.mapi 
    (fun i c -> {fld_name = c.def.commented.def_name ;
                 fld_pos = i; fld_defined = c.def.commented.def_rhs <> None})
    m.redeclared_components

let add_import env import = match import.commented with
  | NamedImport {global=[]; _} | Unnamed [] -> (* cannot happen, make ocamlc happy *) env                                                                    
  (* in the case of a renaming import, pick up the substitution *)
  | NamedImport {global;local} ->
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
  current_path : class_ptr_elem Location.loc DQ.t ;
  anons : int ;
  class_code : class_stmt list ;
  current_field : Syntax.str DQ.t ;
  value_code : value_stmt list ;
  payload_code : payload_stmt list;
}

let rec add_imports imports state = match imports with
    [] -> ((),state)
  | i::imports -> add_imports imports {state with env = add_import state.env i}

let shadow_imports public protected state =
  let name_of = function
    | Short tds -> tds.td_name
    | Composition tds -> tds.td_name
    | Enumeration tds -> tds.td_name
    | OpenEnumeration tds -> tds.td_name
    | DerSpec tds -> tds.td_name
    | Extension tds -> tds.td_name
  in

  let folder = {Syntax.identity_folder with
                fold_typedef = (fun _ td state -> {state with env = StrMap.remove (name_of td.commented).txt state.env}) ;
                fold_definition = (fun _ def state -> {state with env = StrMap.remove def.commented.def_name state.env}) ;
               }
  in

  ((), folder.fold_elements folder public (folder.fold_elements folder protected state))

let return x = fun s -> (x, s)

let bind ma f = fun s -> let (a, s') = ma s in
  (f a s') 

let run m = let (a,s) = m {env = StrMap.empty ; current_path = DQ.empty ; anons = 0; class_code = [];
                           current_field = DQ.empty ; value_code = []; payload_code = []} in a

let down pe state = ((), {state with current_path = DQ.snoc state.current_path pe})

let within_path = function 
    None -> return ()
  | Some (ps) -> fun state -> ((), {state with current_path = DQ.of_list (List.map (fun {loc;txt} -> {loc; txt=`ClassMember txt}) ps)})

let up state = ((), {state with current_path = match DQ.rear state.current_path with None -> DQ.empty | Some (xs,_) -> xs})

let txt_only = DQ.map (fun {txt} -> txt)

let define rhs state = ((), {state with class_code = {lhs=txt_only state.current_path; rhs} :: state.class_code})

let import_mapper env =
  (* resolve imports in expressions *)
  let rec merge x = function
    (* Need to merge all subscripts when replacing an imported name, e.g.,
      import b.a |= a[3] =>  b.a[3] *)
      [] -> raise InconsistentHierarchy
    | [y] -> [{x with ident=y}]
    | y::ys -> {ident=y; subscripts=[]}::(merge x ys)
  in                  
  let map_unknown_ref self = function
      {root=true} as cr -> cr
    | {components=x::xs} when StrMap.mem x.ident.txt env ->
      {root=true; components=(merge x (StrMap.find x.ident.txt env)) @ xs}
    | c -> c
  in
  (* TODO: implement shadowing of imported names by local variables *)
  {Syntax.identity_mapper with map_unknown_ref}

let apply_imports env =
  let mapper = import_mapper env in
  (mapper.map_exp mapper)
  
let payload rhs state =
  (* Small optimization: Only cover actual payload *)
  if rhs.annotated_elem = Syntax_fragments.empty_behavior && rhs.annotation=None then
    ((), state)
  else
    let mapper = import_mapper state.env in
    let map_behavior = mapper.map_behavior mapper in
    let rhs = mapper.map_annotated map_behavior mapper rhs in    
    let state' = {state with payload_code = {lhs=txt_only state.current_path; rhs} :: state.payload_code} in
    ((), state')

let down_field x state = ((), {state with current_field = DQ.snoc state.current_field x})

let up_field state = ((), {state with current_field = match DQ.rear state.current_field with None -> DQ.empty | Some (xs,_) -> xs})

let bind_value rhs state =
  let rhs = apply_imports state.env rhs in
  let () = assert (DQ.size state.current_path > 0) in
  let scope = txt_only state.current_path in
  let field = List.of_enum (Enum.map (fun ident -> {subscripts=[]; ident}) (DQ.enum (state.current_field))) in
  ((), {state with value_code = {lhs = {scope; field}; rhs} :: state.value_code})

let open_class sort elements post state = ((), {state with class_code =
                                                             {lhs = txt_only state.current_path ;
                                                              rhs = Close elements } ::
                                                             {lhs = txt_only state.current_path;
                                                              rhs = (post (Empty {class_sort = sort; class_name = (Name.of_ptr (txt_only state.current_path))}))} :: state.class_code})

let in_context m state =
  let (x, s') = m {state with anons = (Hashtbl.hash state.current_path)} in
  (x, {state with class_code = s'.class_code; value_code = s'.value_code; payload_code = s'.payload_code})

let inside name m state =
  let (x, s') = m {state with current_path = name} in
  (x, {s' with current_path = state.current_path})

let current_path state = (state.current_path, state)

let in_superclass state = match DQ.rear state.current_path with
    Some(xs, {txt=`SuperClass _}) -> (true, state)
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
  | x::xs when StrMap.mem x.txt state.env -> (RootReference ((StrMap.find x.txt state.env) @ xs), state)
  | xs -> (Reference xs, state)

let get state = (state, state)

let set state s = ((), state)

let set_env env state = ((), {state with env})

let next_anon state = (nl (`ClassMember ("anon" ^ (string_of_int state.anons))), {state with anons = state.anons + 1})

let down_class {loc;txt} = down {loc; txt=`ClassMember txt}

let rec mtranslate_typedef td =  
  match td.commented with
  | Short tds -> do_ ;
    (* new path is the definition *)
    down_class tds.td_name ;
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
      shadow_imports tds.type_exp.public tds.type_exp.protected ;
      (* Class name *)
      down_class tds.td_name ;
      (* Class skeleton *)
      open_class tds.sort (order_defs tds.type_exp.public) (repl tds.type_options) ;
      (* Payload *)
      payload {annotated_elem=tds.type_exp.cargo; annotation=td.comment.annotation} ;
      (* Public elements *)
      mtranslate_elements tds.type_exp.public ;	 
      (* Protected elements *)
      down (nl `Protected) ;
      mtranslate_elements tds.type_exp.protected 
    )     

  | Enumeration tds ->
    do_ ;
    down_class tds.td_name ;
    define (repl tds.type_options (sort tds.sort (PEnumeration (StrSet.of_list (List.map (fun {commented} -> commented) tds.type_exp))))) ;
    up

  | OpenEnumeration tds ->
    do_ ;
    down_class tds.td_name ;
    define (repl tds.type_options (sort tds.sort (PEnumeration StrSet.empty))) ;
    up

  | DerSpec tds ->
    do_ ;
    down_class tds.td_name ;
    define (repl tds.type_options (sort tds.sort (Constr {arg = Reference tds.type_exp.der_name ; constr = CDer (lunloc tds.type_exp.idents)}))) ;
    up 

  | Extension tds ->
    let (cmp, _) = tds.type_exp in
    in_context (
      do_ ;
      add_imports cmp.imports ;
      shadow_imports cmp.public cmp.protected ;
      down_class tds.td_name ;
      open_class tds.sort (order_defs cmp.public) (repl tds.type_options) ;
      mtranslate_elements cmp.public ;
      down (nl (`SuperClass (List.length cmp.public.extensions))) ;
      define RedeclareExtends ; up ;
      down (nl `Protected) ;
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
    define (post r)
  | TRootName n -> define (post (RootReference n))

  | TArray {base_type;dims} -> appl base_type (CArray (List.length dims))
  | TVar {flag;flagged} -> appl flagged (CVar flag)                                
  | TCon {flag;flagged} -> appl flagged (CCon flag)
  | TCau {flag;flagged} -> appl flagged (CCau flag)

  | TMod {mod_type; modification} ->
    do_ ;
    state <-- get ;
    let s = state.current_path in
    let (src,ctxt) = match DQ.rear s with None -> raise InconsistentHierarchy | Some(xs,x) -> (xs,x) in
    redec <--
    begin match ctxt.txt with
        `SuperClass _ -> mtranslate_mod_superclass src ctxt {mod_type; modification}
      | `FieldType _ -> mtranslate_mod_field src {mod_type; modification}
      | `ClassMember _ -> mtranslate_mod_class src ctxt {mod_type; modification}
      | `Protected | `Any _ -> raise InconsistentHierarchy
    end ;

    begin
    (* Do not introduce a new class in case of (nested) modifications without redeclarations *)
    if (not redec) then begin
      do_ ;
      set state ;
      mtranslate_texp (fun x -> x) mod_type ;
    end
    else return () ;
    end ;
    
    (* value modifications go into different places, depending on context *)
    begin match ctxt.txt with
        `SuperClass _ -> do_ ; up; mtranslate_modification_values modification; down ctxt 
      | `FieldType txt -> do_ ; up; down_field {loc=ctxt.loc; txt}; mtranslate_modification_values modification; up_field; down ctxt
      | `ClassMember _ -> mtranslate_modification_values modification
      | `Protected | `Any _ -> raise InconsistentHierarchy
    end
    
and mtranslate_mod_class src name {mod_type; modification} =
  (* Modification of a class binding, e.g. 
     'model Pipe = MyCoolPipe(redeclare package Medium = MyCoolMedium)'
  *)    
  do_ ;
  (* context is [..; 'model Pipe'] *)
  open_class Class (order_modified_defs modification) (fun x -> x) ;
  down (nl (`SuperClass 0)) ;
  mtranslate_texp (fun x -> x) mod_type ;
  up ;     
  mtranslate_modification src modification 

and mtranslate_mod_field src {mod_type; modification} =
  (* Modification of a field type, e.g.
     'Pipe pipe(redeclare package Medium = MyCoolMedium)'
     Introduce a new anonymous class, since
     we do not want to create classes with field names
     TODO: maybe use the field name for the anonymous class' name
  *)
  do_ ;
  a <-- next_anon ;  
  let pullout = DQ.snoc src a in     
  (* context is [..; 'field pipe'] *)
  define (KnownPtr (txt_only pullout)) ;
  up ;
  down a ;
  open_class Class (order_modified_defs modification) (fun x -> x) ;
  down (nl (`SuperClass 0)) ;
  mtranslate_texp (fun x -> x) mod_type ;
  up ;     
  mtranslate_modification src modification 
  (* context is [..; 'class anon1234'] *)
    
and mtranslate_mod_superclass src name {mod_type; modification} =
(* In an extends-clause with modifications, we need to 
   separate the superclass from the modification, since
   the modification might use elements from the superclass *)
    do_ ;
  (* context is [..; 'superclass i'] *)
  mtranslate_texp identity mod_type ;
  up ;
  redec <-- mtranslate_modification src modification ;
  (* restore context *)
  down name ;
  return redec 
  
and mtranslate_extends i {ext_type} =
  do_ ;
  down (nl (`SuperClass i)) ;
  mtranslate_texp identity ext_type ;
  up
  
and mtranslate_elements {extensions;typedefs;redeclared_typedefs;defs} = 
  do_ ;
  mseqi mtranslate_extends extensions ;
  mseq mtranslate_typedef typedefs ;
  mseq mtranslate_def defs ;
  mseq mtranslate_typedef redeclared_typedefs

and mtranslate_def def =
  do_ ;
  down (nl (`FieldType def.commented.def_name)) ;
  mtranslate_texp (repl {Syntax_fragments.no_type_options with type_replaceable = def.commented.def_options.replaceable}) def.commented.def_type ;  
  up ;
  down_field (nl def.commented.def_name) ;
  begin match def.commented.def_rhs with
      Some e -> bind_value e
    | None -> return () end ;
  up_field 

and mtranslate_type_redeclaration src {redecl_type} =
  let tds = redecl_type.commented in
  (* a redeclared type is resolved in the parent class scope *)
  do_ ;
  a <-- next_anon ;
  let pullout = DQ.snoc src a in
  inside pullout (mtranslate_texp (final tds.type_options %> sort tds.sort) tds.type_exp ) ;
  down_class tds.td_name ;
  define (KnownPtr (txt_only pullout)) ;  
  up 

and mtranslate_modification src {redeclared_types; redeclared_components; modifications} =
  do_ ;
  mseq (mtranslate_type_redeclaration src) redeclared_types ;
  mseq (mtranslate_def_redeclaration src) redeclared_components ; 
  x <-- mfold false (||) (mtranslate_nested_modification src) modifications ;
  return (x || redeclared_types != [] || redeclared_components != [])

and mtranslate_nested_modification src = function
  | {commented = {mod_name = []; mod_value = None}} -> return false
  | {commented = {mod_name = []; mod_value = Some (Nested nested)}} ->     
    mtranslate_modification src nested
  | {commented = {mod_name =  []; mod_value = Some (NestedRebind {nested})}} ->
    mtranslate_modification src nested ;
  | {commented = {mod_name =  []; mod_value = Some (Rebind _)}} ->
    return false 
  | {commented = {mod_name = x::xs}} as nm ->
    do_ ;
    state <-- get ;
    down {loc=x.loc; txt=(`Any x.txt)} ;
    open_class Class [] (fun x -> x) ;
    down (nl (`SuperClass 0)) ;
    define RedeclareExtends ;
    up;    
    change <-- mtranslate_nested_modification src
      {nm with commented = {nm.commented with mod_name = xs}} ;
    up ;
    if (not change) then begin
      do_ ;
      set state ;
      return false
    end else
      return true    

and mtranslate_def_redeclaration src {def} = do_ ;
  (* a redeclared type is resolved in the parent class scope *)
  f <-- next_anon ;
  let pullout = DQ.snoc src f in
  inside pullout (mtranslate_texp (repl {Syntax_fragments.no_type_options with type_replaceable = def.commented.def_options.replaceable}) def.commented.def_type) ;
  down (nl (`FieldType def.commented.def_name)) ;
  define (KnownPtr (txt_only pullout)) ;  
  up

and mtranslate_nested_modification_values = function
  | {commented = {mod_name = []; mod_value = None}} -> return ()
  | {commented = {mod_name = []; mod_value = Some (Nested nested)}} ->     
    mtranslate_modification_values nested
  | {commented = {mod_name =  []; mod_value = Some (NestedRebind {nested; new_value})}} ->
    do_ ;
    mtranslate_modification_values nested ;
    bind_value new_value
  | {commented = {mod_name =  []; mod_value = Some (Rebind v)}} ->
    bind_value v
  | {commented = {mod_name = x::xs}} as nm ->
    do_ ;
    down_field x;
    mtranslate_nested_modification_values {nm with commented = {nm.commented with mod_name = xs}} ;
    up_field 
           
and mtranslate_modification_values {modifications} =
  mseq mtranslate_nested_modification_values modifications 

type translated_unit = {
  class_name : Name.t;
  class_code : class_stmt list;
  impl_code : value_program ;
  payload : payload_stmt list;
} [@@deriving show,yojson]

open FileSystem

let mtranslate_unit env = function
    {within; toplevel_defs=td::_} ->
    do_ ;
    set_env env ;
    within_path within ;
    mtranslate_typedef td ;
    s <-- get ;
    return {class_code=s.class_code; class_name=Name.of_ptr (txt_only s.current_path); impl_code=s.value_code; payload=s.payload_code}
  | _ -> raise InconsistentHierarchy
           
let translate_unit env {scanned; parsed} =
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




