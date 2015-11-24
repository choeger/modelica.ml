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

(** Normalize a modelica Library's implementation part *)
open Batteries
open Utils
open Syntax
open ModlibInter
open ModlibNormalized
    
type environment_entry = EnvClass of class_value
                       | EnvField of class_value
                       | EnvVar
                         [@@deriving show,eq]

type environment = { public_env : environment_entry StrMap.t ;
                     protected_env : environment_entry StrMap.t }
  [@@deriving show,eq]

let empty_env = {public_env = StrMap.empty ; protected_env = StrMap.empty}

let env_mem x {public_env; protected_env} = StrMap.mem x public_env || StrMap.mem x protected_env

let env_find x {public_env; protected_env} = try StrMap.find x public_env with Not_found -> StrMap.find x protected_env

(** Environment of a class *)
let env_folder lib = { ModlibNormalized.identity_folder with

                       (* Recursively search for global references, TODO: remove and enforce expansion? *)
                       on_class_value = { ModlibNormalized.identity_folder.on_class_value with
                                          fold_GlobalReference =
                                            (fun self cp env -> match ModlibNormalized.lookup_path lib cp with
                                               | `Found f -> self.fold_class_value self f.found_value env
                                               | _ -> env
                                            );
                                        } ;
                                              
                       fold_object_struct =
                         (fun self {public; protected} env ->
                            (* Collect environments of the protected parts and combine to new protected env *)
                            let prot = self.fold_elements_struct self protected empty_env in
                            self.fold_elements_struct self public
                              {env with protected_env = StrMap.union prot.public_env (StrMap.union env.protected_env prot.protected_env)}) ;

                       fold_elements_struct =
                         (fun self {class_members;fields;super} env ->
                            let env' = IntMap.fold (fun _ -> self.fold_class_value self) super env in
                            (* Put parts into public environment by default (see above for the part sorting it out) *)
                            {env' with public_env =
                                         StrMap.union (StrMap.union env'.public_env (StrMap.map (fun v -> EnvClass v) class_members))
                                           (StrMap.map (fun v -> EnvField v.field_class) fields)}
                         )
                     }

let env lib cv =
  let f = env_folder lib in
  f.fold_class_value f cv empty_env 

let os_env lib os =
  let f = env_folder lib in
  f.fold_object_struct f os empty_env

type wip_context = { ctxt_todo : Path.t ;
                     ctxt_classes : object_struct list }
                     
let ctxt_folder lib = { ModlibNormalized.identity_folder with

                        fold_object_struct = (fun self os ctxt ->
                            let ctxt = {ctxt with ctxt_classes = os :: ctxt.ctxt_classes} in
                            match DQ.front ctxt.ctxt_todo with
                              None -> ctxt
                            | Some (`Protected, ctxt_todo) -> self.fold_elements_struct self os.protected {ctxt with ctxt_todo}
                            | Some (_,_) -> self.fold_elements_struct self os.public ctxt
                          ) ;

                        fold_elements_struct = (fun self {class_members} ctxt -> match DQ.front ctxt.ctxt_todo with
                            | Some(`ClassMember x, ctxt_todo) when StrMap.mem x class_members ->
                              self.fold_class_value self (StrMap.find x class_members) {ctxt with ctxt_todo}
                            | _ -> ctxt
                          );
                      }

let lexical_ctxt lib ctxt_todo =
  let f = ctxt_folder lib in
  f.fold_elements_struct f lib {ctxt_classes = []; ctxt_todo}

type lexical_env = environment list [@@deriving show,eq]

let lexical_env lib path =
  let ctxt = lexical_ctxt lib path in
  List.map (os_env lib) ctxt.ctxt_classes

(** A stratified value binding *)
type strat_stmt = { field_name : string DQ.t;
                    exp : Syntax.exp } [@@deriving show]

type strat_stmts = strat_stmt list PathMap.t

type impl_state = { strat_stmts : strat_stmts ; current_env : lexical_env ; current_path : Path.t }

exception NoSuchField of str
exception DoubleModification of string
exception AstInvariant
exception SubscriptsOnClass of str
exception NoSuchClass of str
exception ProjectFromFunction of str

let rec resolve_os lib class_name os x xs =
  (* Resolve a reference in an object structure *)
  match ModlibLookup.get_class_element_os lib DQ.empty os x.ident.txt DQ.empty with
    `Found {found_value; found_path} ->
    begin match DQ.rear found_path with
      | Some(_, `ClassMember _) -> resolve_in lib (DQ.snoc class_name x.ident.txt) found_value xs
      | Some(_, `FieldType _) -> {class_name; fields=DQ.of_list (x::xs)}
      | _ -> raise AstInvariant
    end
  | _ -> raise (NoSuchField x.ident)

and resolve_in lib class_name cv (components : component list) = match components with
    [] -> {class_name; fields = DQ.empty}
  | x :: xs -> begin match cv with
      | Class os when x.subscripts=[] -> resolve_os lib class_name os x xs
      (* Everything else cannot denote a class or function *)
      | Class _ 
      | Int | Real | String | Bool | Unit | ProtoExternalObject | Enumeration _ -> {class_name; fields=DQ.of_list components}
    end

let rec resolve_env lib class_name first rest = function
    [] -> resolve_os lib DQ.empty {empty_object_struct with public=lib} first rest
  | env :: envs when env_mem first.ident.txt env ->
    begin
    match env_find first.ident.txt env with
      EnvClass cv when first.subscripts = [] -> resolve_in lib (DQ.snoc class_name first.ident.txt) cv rest
    | EnvClass cv -> raise (SubscriptsOnClass first.ident)
    | EnvField cv -> {class_name; fields = DQ.of_list rest}
    | EnvVar -> {class_name = DQ.empty; fields = DQ.of_list (first :: rest)}
    end
  | env :: envs -> begin
      (* try next scope *)
      match DQ.rear class_name with None -> raise AstInvariant
                                  | Some (xs,_) -> resolve_env lib xs first rest envs
    end
    
let resolve_ur lib src env {root;components} =
  match components with
    cmp :: components ->
      if root then
        resolve_os lib DQ.empty {empty_object_struct with public=lib} cmp components
      else
        resolve_env lib src cmp components env 
  | [] -> raise AstInvariant

let resolution_mapper lib src env = { Syntax.identity_mapper with
                                      on_component_reference = {
                                        Syntax.identity_mapper.on_component_reference with
                                        map_UnknownRef =
                                          (fun _ ur -> KnownRef (resolve_ur lib src env ur));
                                      }
                                    }

let rec resolve lib src env exp = let m = resolution_mapper lib src env in
  m.map_exp m exp

let rec merge_mod exp mod_name nested_name mods =
  if StrMap.mem mod_name mods then
    let new_mod =
    match StrMap.find mod_name mods with
      Modify _ -> raise (DoubleModification mod_name)
    | Nested mods -> 
      begin match DQ.front nested_name with
        | None when mods = StrMap.empty -> Modify exp
        | None -> raise (DoubleModification mod_name)
        | Some (x,xs) -> Nested (merge_mod exp x xs mods)
      end
      in StrMap.add mod_name new_mod mods
  else
    merge_mod exp mod_name nested_name (StrMap.add mod_name (Nested StrMap.empty) mods)
      
let rec normalize_stmts lib src env class_fields = function
  | [] -> class_fields
  | {field_name;exp}::stmts ->
    let exp = resolve lib src env exp in
    begin match DQ.front field_name with    
      | Some (x,xs) when StrMap.mem x class_fields ->
        let fld = StrMap.find x class_fields in
        let class_field = 
        match DQ.front xs with
          None -> {fld with field_binding = Some exp}
        | Some(y,ys) -> {fld with field_mod = merge_mod exp y ys fld.field_mod} 
        in normalize_stmts lib src env (StrMap.add x class_field class_fields) stmts
      | None -> normalize_stmts lib src env class_fields stmts (* bogus stmt *)
      | Some (x, xs) ->        
        BatLog.logf "No field %s in %a\n" x (DQ.print IO.write_string) src ;
        raise (NoSuchField ({txt=x;loc=Location.none})) (* Error TODO: move to Report Monad? *)
    end

let rec impl_mapper lib {strat_stmts; current_env; current_path} =
  let class_name path = DQ.of_enum (Enum.filter_map (function `ClassMember x -> Some x | _ -> None) (DQ.enum path)) in
  
  { ModlibNormalized.identity_mapper with
    
    map_object_struct = (fun self os ->       
        (* Update the environment for each object struct *)
        let pub_state = {
            strat_stmts ;
            current_env = (os_env lib os)::current_env;
            current_path = os.source_path }
        in
        let s = impl_mapper lib pub_state in
        let public = s.map_elements_struct s os.public in

        let s = impl_mapper lib {pub_state with current_path = DQ.snoc pub_state.current_path `Protected} in
        let protected = s.map_elements_struct s os.protected in
        {os with public; protected});

    map_elements_struct = (fun self {class_members; super; fields} ->
        let stmts = if PathMap.mem current_path strat_stmts then PathMap.find current_path strat_stmts else [] in        
        (* proceed through the tree *)
        let class_members = StrMap.map (self.map_class_value self) class_members in

        (* normalize and attach statements to fields *)
        let fields = normalize_stmts lib (class_name current_path) current_env fields stmts in
        {class_members; super; fields}
      );
  }

let norm lib strat_stmts =
  let m = impl_mapper lib {strat_stmts; current_env = []; current_path = DQ.empty} in
  m.map_elements_struct m lib
                                      
