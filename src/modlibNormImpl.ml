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
open ModlibLookup
    
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
                            let env' = IntMap.fold (fun _ -> self.fold_modified_class self) super env in
                            (* Put parts into public environment by default (see above for the part sorting it out) *)
                            {env' with public_env =
                                         StrMap.union (StrMap.union env'.public_env (StrMap.map (fun v -> EnvClass v.class_) class_members))
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
                              self.fold_class_value self (StrMap.find x class_members).class_ {ctxt with ctxt_todo}
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
type strat_stmt = { field_name : known_ref ;
                    exp : Syntax.exp } [@@deriving show]

type strat_stmts = strat_stmt list PathMap.t

type payload_stmts = Syntax.behavior PathMap.t

type impl_state = { notify : Path.t -> unit ;
                    strat_stmts : strat_stmts ; payload : payload_stmts ;
                    current_env : lexical_env ; current_path : Path.t }

exception NoSuchField of str
exception DoubleModification of string
exception AstInvariant
exception SubscriptsOnClass of str
exception NoSuchClass of str
exception ProjectFromFunction of str

let ck_of_var = 
  let open Flags in
  function None -> CK_Continuous | Some Constant -> CK_Constant | Some Parameter -> CK_Parameter | Some Discrete -> CK_Discrete

let rec extends_builtin lib = function
  | Class os -> extends_builtin_os lib os
  | GlobalReference p -> begin match lookup_path lib p with
            `Found {found_value} -> extends_builtin lib found_value
          | _ -> raise (Failure "Lookup error")
    end
  | Replaceable arg | Constr {arg} -> extends_builtin lib arg
  | Int | Real | String | Bool | Unit -> true
  | _ -> false
    
and extends_builtin_os lib {object_sort; public; protected} =
  object_sort = Type && (
   (* TODO: protected.super = IntMap.empty ? *)
    (extends_builtin_el lib public) || (extends_builtin_el lib protected))
  
and extends_builtin_el lib {super} = IntMap.cardinal super = 1 && extends_builtin lib (IntMap.find 0 super).class_

let rec resolve_os lib found os x xs =    
  (* Resolve a reference in an object structure *)
  match ModlibLookup.get_class_element_os lib DQ.empty os x.ident.txt DQ.empty with
    `Found {found_value; found_path} ->
    begin match DQ.rear found_path with
      | Some(_, `ClassMember _) ->
        resolve_in lib (DQ.snoc found {kind = CK_Class ; component=x}) found_value xs
          
      | Some(_, `FieldType _) ->
        let {flat_attr={fa_var}} = flat found_value in
        let kind = ck_of_var fa_var in
        resolve_in lib (DQ.snoc found {kind ; component=x}) found_value xs
      | _ -> raise AstInvariant
    end
  | `NothingFound when extends_builtin_os lib os ->
    DQ.append found (DQ.of_list (List.map (fun component -> {kind=CK_BuiltinAttr; component}) (x::xs)))
  | _ -> BatLog.logf "In:\n %s\n" (Path.show os.source_path) ;
    BatLog.logf "NoSuchField: %s\n" (show_component x) ;
    raise (NoSuchField x.ident)

and resolve_in lib found cv (components : component list) = match components with
    [] -> found
  | x :: xs -> begin match cv with
      | Recursive _ -> raise (Failure "Cannot normalize recursive type")
      | DynamicReference p | GlobalReference p ->
        begin match lookup_path lib p with
            `Found {found_value} -> resolve_in lib found found_value components
          | _ -> raise (Failure "Lookup error")
        end
      | Replaceable arg | Constr {arg} -> resolve_in lib found arg components
      | Class os when x.subscripts=[] -> resolve_os lib found os x xs
      (* Everything else has only builtin attributes *)
      | Class _ 
      | Int | Real | String | Bool | Unit | ProtoExternalObject | Enumeration _ ->
        DQ.append (DQ.snoc found {kind=CK_BuiltinAttr; component=x})
          (DQ.of_list (List.map (fun component -> {kind=CK_BuiltinAttr; component}) xs ))
    end

(** Attempt to resolve $first.$rest as a builtin *)
let resolve_builtin lib first rest =
  let builtin kind = DQ.cons {kind; component=first} (DQ.of_list (List.map (fun component -> {kind=CK_BuiltinAttr; component}) rest)) in
  match first.ident.txt with
  (* Free variable *)
  | "time" -> builtin CK_Time
                
  (* Numeric Functions and Conversion Functions, see 3.7.1 *)
  | "abs" | "sign" | "sqrt" | "div" 
  | "mod" | "rem" | "ceil" | "floor" 
  | "integer"
  (* 3.7.1.2 *)
  | "sin" | "cos" | "tan"
  | "asin" | "acos" | "atan"
  | "atan2" 
  | "sinh" | "cosh" | "tanh"
  | "exp" | "log" | "log10"
    -> builtin CK_BuiltinFunction

  (* Reductions, see 10.3.4 *)
  | "min" | "max" | "sum" | "product"
    -> builtin CK_BuiltinFunction

  (* Event related *)
  | "noEvent" -> builtin CK_BuiltinFunction
  | "smooth" -> builtin CK_BuiltinFunction

  (* Array functions, see 10.3 *)
  | "size" | "ndims" -> builtin CK_BuiltinFunction
  | "scalar" | "vector" | "matrix" -> builtin CK_BuiltinFunction
  | "zeros" | "fill" | "ones" | "identity" | "diagonal" -> builtin CK_BuiltinFunction

  (* Builtin Classes *)
  | "String" -> builtin CK_BuiltinClass
  | "StateSelect" -> builtin CK_BuiltinClass

  (* TODO: this is actually wrong, the toplevel should come _before_ the builtins *)
  | _ -> resolve_os lib DQ.empty {empty_object_struct with public=lib} first rest 

let rec resolve_env lib found first rest = function
    [] -> resolve_builtin lib first rest
  | env :: envs when env_mem first.ident.txt env ->
    begin
    match env_find first.ident.txt env with
      EnvClass cv when first.subscripts = [] -> resolve_in lib (DQ.snoc found {kind=CK_Class; component=first}) cv rest
    | EnvClass cv -> raise (SubscriptsOnClass first.ident)
    | EnvField cv ->
      let {flat_attr={fa_var}} = flat cv in
      let kind = ck_of_var fa_var in      
      resolve_in lib (DQ.snoc found {kind; component=first}) cv rest                                                     
    | EnvVar -> (* found a local variable, its elements can only be checked by type-inference *)
      DQ.cons {kind=CK_LocalVar; component=first} (DQ.of_list (List.map (fun component -> {kind=CK_VarAttr; component}) rest))
    end
  | env :: envs -> begin
      (* try next scope 
         variable found contains the candidate prefix, i.e. the name of the class of the current scope
      *)
      match DQ.rear found with None -> raise AstInvariant
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

let rec resolution_mapper lib src env = { Syntax.identity_mapper with
                                          on_component_reference = {
                                            Syntax.identity_mapper.on_component_reference with
                                            map_UnknownRef = (fun _ ur -> KnownRef (resolve_ur lib src env ur));
                                          } ;

                                          map_for_statement = 
                                            (fun self {idx; body} ->
                                               let idx = List.map (self.map_idx self) idx in
                                               let mk_env = fun {variable={txt}} m -> StrMap.add txt EnvVar m in
                                               let env = match env with [] -> env (* cannot happen, one env per class *)
                                                                      | e::es -> {e with public_env = List.fold_right mk_env idx e.public_env}::es
                                               in
                                               let self' = resolution_mapper lib src env  in
                                               let body = self'.map_statements self' body in
                                               {idx; body}) ;

                                          map_for_equation =
                                            (fun self {idx; body} ->
                                               let idx = List.map (self.map_idx self) idx in
                                               let mk_env = fun {variable={txt}} m -> StrMap.add txt EnvVar m in
                                               let env = match env with [] -> env (* cannot happen, one env per class *)
                                                                      | e::es -> {e with public_env = List.fold_right mk_env idx e.public_env}::es
                                               in
                                               let self' = resolution_mapper lib src env  in
                                               let body = self'.map_equations self' body in
                                               {idx; body}) ;
                                            
                                        }

let resolve lib src env exp =
  let m = resolution_mapper lib src env in
  m.map_exp m exp

let resolve_behavior lib src env =
  let m = resolution_mapper lib src env in
  m.map_behavior m

let stratify_stmt lib scope field exp =
  let components = List.map (fun ident -> {ident;subscripts=[]}) field in
  let () = assert (DQ.size scope > 0) in
  let scope = match DQ.rear scope with
    | Some(xs, `Protected) -> xs (* If we are in the protected section, make sure the scope is a valid class pointer *)
    | _ -> scope
  in
  match lookup_path lib scope with
    `Found {found_value} ->
    let field_name = resolve_in lib DQ.empty found_value components in    
    {field_name; exp}
  | _ -> raise (Failure "Cannot find context of value binding")

(* 
   Merge modification [| $mod_name [.$nested_name] = $exp |] with a component into $mods 
*)
let rec merge_mod exp mod_component nested_component mods =
  let mod_name = mod_component.component.ident.txt in
  if StrMap.mem mod_name mods then
    let new_mod =
      match StrMap.find mod_name mods with
      (* No need to search for the matching component again, reuse from $mods *)
        {mod_desc=Modify _} -> raise (DoubleModification mod_name)
      | {mod_kind; mod_desc=Nested mods} -> 
        begin match DQ.front nested_component with
          | None when mods = StrMap.empty -> {mod_kind; mod_desc=Modify exp}
          | None -> raise (DoubleModification mod_name)
          | Some (x,xs) -> {mod_kind; mod_desc = Nested (merge_mod exp x xs mods)}
        end
    in StrMap.add mod_name new_mod mods
  else
    let empty_mod = {mod_desc = Nested StrMap.empty ; mod_kind = mod_component.kind} in
    merge_mod exp mod_component nested_component (StrMap.add mod_name empty_mod mods)

let rec find_super_field lib x super =
  (* Get the first inherited class field named x or None *)
  let rec take enum = Enum.get (Enum.filter_map get_fld enum)
  and get_fld {class_; class_mod} = match class_ with
      Class os when StrMap.mem x os.public.fields -> Some (StrMap.find x os.public.fields)
    | Class os when StrMap.mem x os.protected.fields -> Some (StrMap.find x os.protected.fields)
    | Class os -> take (Enum.append (IntMap.values os.public.super) (IntMap.values os.protected.super))
    | GlobalReference r ->
      begin match lookup_path lib r with
          `Found {found_value} -> get_fld {class_=found_value; class_mod}
        | _ -> None
      end
    | _ -> None
  in
  take (IntMap.values super)

(* Normalize all statements in a direct class modification *)
let rec normalize_classmod_stmts lib src env {class_; class_mod} =
  function
  | [] -> {class_; class_mod}
  | {field_name; exp}::stmts ->
    (* normalize the modified component *)
    let exp = resolve lib src env exp in

    (* merge modification and continue *)
    let class_mod =
    begin match DQ.front field_name with
        None -> raise (Failure "empty modification on class")
      | Some(y,ys) -> merge_mod exp y ys class_mod
    end in
    normalize_classmod_stmts lib src env {class_; class_mod} stmts

(* Normalize all statements in the given element structure *)
let rec normalize_stmts lib src env ({super;fields;class_members} as es)=
  function
  | [] -> es
  | {field_name;exp}::stmts ->
    (* normalize the modified component *)
    let exp = resolve lib src env exp in

    let insert fld xs = match DQ.front xs with
        None -> {fld with field_binding = Some exp}
      | Some(y,ys) -> {fld with field_mod = merge_mod exp y ys fld.field_mod} 
    in
    
    begin match DQ.front field_name with
      | None -> normalize_stmts lib src env es stmts (* bogus stmt *)                  

      (* TODO: nested modification inside classes *)                 
      
      (* Local field *)
      | Some ({kind=CK_Constant | CK_Continuous | CK_Parameter | CK_Discrete; component},xs) when StrMap.mem component.ident.txt fields ->
        let fld = StrMap.find component.ident.txt fields in
        let class_field = insert fld xs 
        in normalize_stmts lib src env {es with fields = StrMap.add component.ident.txt class_field fields} stmts

      (* Inherited field *)
      | Some ({kind=CK_Constant | CK_Continuous | CK_Parameter | CK_Discrete; component},xs) ->
        (* Search superclasses *)
        begin match find_super_field lib component.ident.txt super with
            None -> BatLog.logf "No field %s in %a\n" (show_component component) (DQ.print (fun x c -> IO.write_string x (show_known_component c))) src ;
            raise (NoSuchField component.ident) (* Error TODO: move to Report Monad? *)
          | Some fld ->
            (* TODO: this only works properly when a modification of the inherited field is found *)
            let class_field = insert fld xs 
            in normalize_stmts lib src env {es with fields = (StrMap.add component.ident.txt class_field fields)} stmts
        end

      | Some(x,_) -> raise (Failure ("Don't know how to handle " ^ (show_known_component x)))
    end

let rec impl_mapper lib {notify; strat_stmts; payload; current_env; current_path} =
  let class_name path = DQ.of_enum (Enum.filter_map (function `ClassMember x -> Some {kind=CK_Class;component={ident={txt=x;loc=Location.none};subscripts=[]}} | _ -> None) (DQ.enum path)) in
  
  { ModlibNormalized.identity_mapper with
    
    map_object_struct = (fun self os ->
        (* Update the environment with the object struct *)
        let current_env = (os_env lib os)::current_env in
        let behavior =
          if PathMap.mem os.source_path payload
          then
            let () = notify os.source_path in
            resolve_behavior lib (class_name os.source_path) current_env (PathMap.find os.source_path payload)
          else
            os.behavior
        in

        let pub_state = {
          notify;
          strat_stmts ;
          payload;
          current_env ;
          current_path = os.source_path }
        in
        let s = impl_mapper lib pub_state in

        let public = s.map_elements_struct s os.public in

        let s = impl_mapper lib {pub_state with current_path = DQ.snoc pub_state.current_path `Protected} in
        let protected = s.map_elements_struct s os.protected in
        {os with public; protected; behavior});

    map_elements_struct = (fun self {class_members; super; fields} ->
        let stmts = if PathMap.mem current_path strat_stmts then PathMap.find current_path strat_stmts else [] in        
        
        (* deal with modified short-defined classes *)
        let map_cm name {class_; class_mod} =
          (* filter out classes with own scope *)
          let rec own_scope = function
              Class _ | Enumeration _ -> true
            | Replaceable arg | Constr {arg} -> own_scope arg
            | _ -> false
          in
          if own_scope class_ then
            (* proceed through the tree *)
            let class_ = self.map_class_value self class_ in
            {class_; class_mod}
          else
            let current_path = DQ.snoc current_path (`ClassMember name) in
            let stmts = if PathMap.mem current_path strat_stmts then PathMap.find current_path strat_stmts else [] in
            normalize_classmod_stmts lib (class_name current_path) current_env {class_;class_mod} stmts
        in
            
        let class_members = StrMap.mapi map_cm class_members in
          
        (* normalize and attach statements to fields *)
        let current_class = class_name current_path in
        normalize_stmts lib current_class current_env {super;fields;class_members} stmts
      );
  }

let norm lib notify payload strat_stmts =
  let m = impl_mapper lib {notify; strat_stmts; payload; current_env = []; current_path = DQ.empty} in
  m.map_elements_struct m lib
                                      
