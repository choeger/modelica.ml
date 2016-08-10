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
    
type strat_stmt = { field_name : components ;
                    exp : Syntax.exp } [@@deriving show]

(** Stratified value bindings *)
type strat_stmts = strat_stmt list PathMap.t

type payload_stmts = Syntax.behavior Syntax.annotated PathMap.t

type impl_state = { notify : Path.t -> unit ;
                    strat_stmts : strat_stmts ; payload : payload_stmts ;
                    current_stmts : strat_stmt list ; current_class : lnode }

exception NoSuchField of str
exception DoubleModification of str
exception SubscriptsOnClass of str
exception NoSuchClass of str
exception ProjectFromFunction of str
(*

let rec extends_builtin lib = function
  | Class os -> extends_builtin_os lib os
  | GlobalReference p -> begin match follow_path lib DQ.empty global with
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
*)

(** Attempt to resolve $first.$rest as a builtin *)
let resolve_builtin first rest =
  let ft_of_attr p = function
      {ident={txt="start" | "min" | "max" | "nominal"}} -> p
    | {ident={txt="quantity" | "unit" | "displayUnit"}} -> Some FTString
    | {ident={txt="stateSelect"}} ->
      Some (FTEnum (StrSet.of_list ["never";"avoid";"default";"prefer";"always"]))
    | {ident={txt="fixed"}} -> Some FTBool
    | {ident={txt}} ->
      begin match p with
          Some (FTEnum xs) when StrSet.mem txt xs -> p
        | _ -> raise (Failure (txt ^ " is not a valid attribute"))
      end
  in

  let builtin ?known_type kind =
    RootRef (DQ.cons {kind; component=first; known_type}
               (DQ.of_list (List.map (fun component -> {kind=CK_BuiltinAttr; known_type=ft_of_attr known_type component; component}) rest)))
  in
  match first.ident.txt with
  (* Free variable *)
  | "time" -> builtin ~known_type:FTReal CK_Time
                
  (* Numeric Functions and Conversion Functions, see 3.7.1 *)
  | "sign" | "sqrt" | "div" 
  | "mod" | "rem" | "ceil" | "floor" 
  | "integer"
  (* 3.7.1.2 *)
  | "abs" | "sin" | "cos" | "tan"
  | "asin" | "acos" | "atan"
  | "atan2" 
  | "sinh" | "cosh" | "tanh"
  | "exp" | "log" | "log10"
    -> builtin ~known_type:(FTFunction ([{ftarg_name="x"; ftarg_type=FTReal; ftarg_opt=false}], [FTReal])) CK_BuiltinFunction

  (* Reductions, see 10.3.4 *)
  | "min" | "max" | "sum" | "product"
    -> builtin CK_BuiltinFunction

  (* 10.3.5 Matrix and Vector Algebra Functions *)
  | "transpose" | "outerProduct" | "symmetric" | "cross" | "skew"
    -> builtin CK_BuiltinFunction

  (* Special, see 3.7.2 *)
  | "inStream" -> builtin ~known_type:(FTSpecial SRInStream) CK_BuiltinFunction
  | "actualStream" -> builtin ~known_type:(FTSpecial SRActualStream) CK_BuiltinFunction
                    
  | "delay" | "cardinality" | "homotopy" | "semiLinear" 
  | "spatialDistribution"
  | "getInstanceName"
    -> builtin CK_BuiltinFunction

  (* Event related, see 3.7.3 *)
  | "noEvent" | "smooth" | "terminal"
  | "sample" | "pre" | "edge" | "change" | "reinit"
    -> builtin CK_BuiltinFunction

  (* 8.3.8 *)
  | "terminate" -> builtin CK_BuiltinFunction

  (* Array functions, see 10.3 *)
  | "size" | "ndims" -> builtin CK_BuiltinFunction
  | "scalar" | "vector" | "matrix" -> builtin CK_BuiltinFunction
  | "array" | "cat" | "zeros" | "fill" | "ones" | "identity" | "diagonal" | "linspace" -> builtin CK_BuiltinFunction

  (* Builtin Classes *)
  | "Boolean" | "Integer" | "String" | "Connections" -> builtin CK_BuiltinClass
  | "StateSelect" -> builtin ~known_type:(FTEnum (StrSet.of_list ["never";"avoid";"default";"prefer";"always"])) CK_BuiltinClass
  | "AssertionLevel" -> builtin ~known_type:(FTEnum (StrSet.of_list ["warning"; "error"])) CK_BuiltinClass

  | _ ->
    BatLog.logf "%s\nError searching for %s\n" (where_desc first.ident.loc) first.ident.txt ; raise (NoSuchClass first.ident)

exception ResolutionError of lookup_error_struct

let rec resolve_env env self first rest =
  if StrMap.mem first.ident.txt env then
    KnownRef {
      scope = 0;
      known_components =
        DQ.cons {kind=CK_LocalVar; known_type = None; component=first} (DQ.of_list (List.map (fun component -> {kind=CK_VarAttr; component; known_type=None}) rest))
    }
  else
    let state = state_of_self self in
    match lookup_lexical_in state first rest with
      Success {lookup_success_state={current_ref}} -> KnownRef current_ref

    | Error {lookup_error_state={self={up=None}}} ->
      resolve_builtin first rest

    | Error {lookup_error_todo=x::_} ->
      BatLog.logf "No field %s in %s.\n" x.ident.txt (show_object_struct self.tip.clbdy) ;
      raise (NoSuchField x.ident)
    | Error _ -> raise (Failure "Lookup failed with empty todo...")
    
let resolve_ur env self {root;components} =
  match components with
    cmp :: components ->
    if root then      
      match  resolve_env StrMap.empty {tip=root_class_of self;up=None} cmp components with
        RootRef kcs -> RootRef kcs
      | KnownRef {known_components; scope=0} -> RootRef known_components
      | _ -> raise (Failure "Lookup went out of scope")               
    else
      resolve_env env self cmp components
  | [] -> raise AstInvariant

type opt_exp = exp option [@@deriving show]

let add_idx env idx = 
  let mk_env = fun {variable={txt};range} m ->
    StrMap.add txt range m in
  List.fold_right mk_env idx env


let rec resolution_mapper env history = { Syntax.identity_mapper with
                                          dispatch_component_reference = {
                                            Syntax.identity_mapper.dispatch_component_reference with
                                            map_UnknownRef = (fun _ ur -> resolve_ur env history ur);
                                          } ;

                                          (* Do not attempt resolution inside annotations, this is futile 
                                             TODO: handle standardized annotations
                                          *)
                                          map_annotated = (fun f _ a -> {a with annotated_elem = f a.annotated_elem}) ;

                                          map_comprehension =
                                            (fun s {exp; idxs} ->
                                               let self' = resolution_mapper (add_idx env idxs) history in
                                               {idxs=List.map (self'.map_idx self') idxs; exp=self'.map_exp self' exp});
                                          
                                          map_for_statement = 
                                            (fun self {idx; body} ->
                                               let self' = resolution_mapper (add_idx env idx) history in
                                               let idx = List.map (self.map_idx self) idx in
                                               let body = self'.map_statements self' body in
                                               {idx; body}) ;

                                          map_for_equation =
                                            (fun self {idx; body} ->
                                               let self' = resolution_mapper (add_idx env idx) history in
                                               let idx = List.map (self.map_idx self) idx in
                                               let body = self'.map_equations self' body in
                                               {idx; body}) ;                                            
                                        }

let resolve env history =
  let m = resolution_mapper env history in
  m.map_exp m

(* 
   Merge modification [| $mod_name [.$nested_name] = $exp |] with a component into $mods 
*)
let rec merge_mod exp mod_component nested_component mods =
  let mod_name = mod_component.component.ident.txt in
  if StrMap.mem mod_name mods then
    let new_mod =
      match StrMap.find mod_name mods with
      (* No need to search for the matching component again, reuse from $mods *)
      | {mod_kind; mod_nested; mod_default} -> 
        begin match DQ.front nested_component with
          | None -> begin match mod_default with
                None -> {mod_kind; mod_nested; mod_default=Some exp}
              | _ ->
                raise (DoubleModification mod_component.component.ident)
            end
          | Some (x,xs) -> {mod_kind; mod_default; mod_nested = merge_mod exp x xs mod_nested}
        end
    in StrMap.add mod_name new_mod mods
  else
    let empty_mod = {mod_default=None; mod_nested=StrMap.empty ; mod_kind = mod_component.kind} in
    merge_mod exp mod_component nested_component (StrMap.add mod_name empty_mod mods)

let rec norm_annotation history =
  let known_annotation = function
      "__amsun" | "__ModelicaAssociation" | "experiment" -> true | _ -> false
  in
  
  function
    [] -> StrMap.empty
    (* Only normalize known annotations for now *)
  | {commented={mod_name=[ident];
                mod_value=Some (Nested {modifications})}}::ms when known_annotation ident.txt ->

    let rec norm_nested field_mods = function
        {commented={mod_name=[l2]; mod_value=Some(Rebind e)}} :: mods ->
        (* Resolve all unquoted expressions *)
        let r = resolution_mapper StrMap.empty history in
        let map_unquote self {fun_; args; named_args} =
          match fun_ with
            UnknownRef {root=false; components=[{ident; subscripts=[]}]} when ident.txt="unquote" ->
            App {fun_; args=List.map (r.map_exp r) args;
                 named_args=List.map (r.map_named_arg r) named_args}
          | r -> 
            App {fun_; args=List.map (self.map_exp self) args; named_args}
        in
    
        let annotation_mapper = {Syntax.identity_mapper with
                                 dispatch_exp = {Syntax.identity_mapper.dispatch_exp with
                                                 map_App = map_unquote
                                                }
                                } in
        let e' = annotation_mapper.map_exp annotation_mapper e in
        let field_mods' = StrMap.add l2.txt             
            {mod_kind=CK_BuiltinClass;
             mod_default = Some e';
             mod_nested = StrMap.empty;
            }
            field_mods 
        in
        norm_nested field_mods' mods

      | {commented={mod_name=[l2]; mod_value=Some (Nested {modifications})}}::mods ->
        let mod_nested = norm_nested StrMap.empty modifications in
        
        let rec merge_mods k {mod_kind; mod_nested;mod_default} mods =
          if StrMap.mem k mods then
            let mod2 = StrMap.find k mods in
            let mod_nested = StrMap.fold merge_mods mod_nested mod2.mod_nested in
            let mod_default =
            match mod_default with
              None -> mod2.mod_default
            | Some e ->
              begin match mod2.mod_default with None -> Some e
                                              | _ -> raise (DoubleModification l2)
              end
            in
            StrMap.add k {mod2 with mod_nested; mod_default} mods
          else
            StrMap.add k {mod_kind;mod_nested;mod_default} mods
        in

        norm_nested (merge_mods l2.txt {mod_kind=CK_BuiltinClass; mod_nested; mod_default=None} field_mods) mods          
      | _ :: mods ->
        (* Cannot handle the unknown shape *)
        norm_nested field_mods mods
      | [] -> field_mods
    in
    StrMap.add ident.txt {mod_kind = CK_BuiltinClass; mod_default=None; mod_nested=norm_nested (norm_annotation history ms) modifications}
      (norm_annotation history ms)
      
  | _::ms -> norm_annotation history ms
    
    

exception ModificationTargetNotFound of components

(* Normalize all statements in a direct class modification *)
let rec normalize_classmod_stmts self kind {class_; class_mod} =
  function
  | [] -> {class_; class_mod}
  | {field_name=[]}::_ -> raise (Failure "empty modification on class")
  | {field_name; exp}::stmts ->
    (* normalize the modified component *)
    let field_name = match get_class_element (state_of_self self) kind class_  field_name with
        Success {lookup_success_state={current_ref}} -> current_ref.known_components
      | Error {lookup_error_todo=todo} ->
        BatLog.logf "Could not find: %s\n" (show_components todo) ;
        raise (ModificationTargetNotFound todo)
    in
    let exp = resolve StrMap.empty self exp in

    (* merge modification and continue *)
    let class_mod =
    begin match DQ.front field_name with
        None -> raise (Failure "empty modification on class")
      | Some(y,ys) -> merge_mod exp y ys class_mod
    end in
    normalize_classmod_stmts self kind {class_; class_mod} stmts

(* Normalize all statements in the given element structure *)
let rec normalize_stmts self ({super;fields;class_members} as es)=
  function
  | [] -> es
  | {field_name=[]}::stmts ->
    (* Should not happen, but we can ignore it *)
    normalize_stmts self es stmts
      
  | {field_name=y::ys;exp}::stmts ->
    (* normalize the modified component *)
    let exp = resolve StrMap.empty self exp in
    (* Lookup with an empty path to get the _relative_ result *)
    match get_class_element_in {(state_of_self self) with current_path = Path.empty} es y ys with
    | Success {lookup_success_state={current_ref; current_path}} ->
      let rec fst p = match Path.front p with
        | None -> raise (Failure "Internal Error: Empty Path")
        | Some(`Protected, p) -> fst p
        | Some(f,_) -> f
      in
      begin match fst current_path with
          `Protected -> raise (Failure "Internal Error: Unexpected end of path")
        | `ClassMember x ->
          begin match Path.front current_ref.known_components with
              Some({kind=CK_Class; component}, cr) ->
              (* Modified a class *)
              let {class_;class_mod} = StrMap.find x class_members in
              (* merge modification and continue *)
              let class_mod =
                begin match DQ.front cr with
                    None -> raise (Failure "empty modification on class")
                  | Some(y,ys) -> merge_mod exp y ys class_mod
                end in
              normalize_stmts self {es with class_members = StrMap.add x {class_;class_mod} class_members} stmts

            | Some(kc,_) -> raise (Failure ("Expected to modify a class " ^ x ^ ", got: " ^ (show_known_component kc)))
            | None -> raise (Failure "Lookup Result inconsistent")
          end
        | `FieldType x ->
          begin match Path.front current_ref.known_components with
            | Some({kind=CK_Class},_) -> raise (Failure ("Expected to modify a component when modifying " ^ x))

            | Some({kind = mod_kind; component}, cr) ->
              (* Modified a field *)
              let insert fld xs = match DQ.front xs with
                  None -> {fld with field_mod = {mod_kind; mod_default=Some exp; mod_nested=fld.field_mod.mod_nested}}
                | Some(y,ys) -> {fld with field_mod = {fld.field_mod with mod_kind; mod_nested = merge_mod exp y ys fld.field_mod.mod_nested}} 
              in
              let fld = StrMap.find x fields in
              (* merge modification and continue *)
              let class_field = insert fld cr in
              normalize_stmts self {es with fields = StrMap.add x class_field fields} stmts
                
            | None -> raise (Failure "Lookup Result inconsistent")
          end
        | `SuperClass n ->
          begin match Path.front current_ref.known_components with
              Some(y,ys) ->
              let {super_mod} as sc = IntMap.find n super in
              let super_mod = merge_mod exp y ys super_mod in
              normalize_stmts self {es with super = IntMap.add n {sc with super_mod} super} stmts
            | None -> raise (Failure "Lookup Result inconsistent")
          end
      end
    | Error {lookup_error_todo=todo} ->
      let () = BatLog.logf "Error looking up modification target %s\n" (show_components todo) in
      raise (ModificationTargetNotFound todo)


let rec impl_mapper {notify; strat_stmts; payload; current_class; current_stmts} =  
  { ModlibNormalized.identity_mapper with
    
    map_object_struct = (fun self os ->
        (* Update the lookup environment *)
        let current_class = {tip={clup=Some current_class; clbdy=os}; up=Some current_class}          
        in
        let (behavior, annotation) =
          if PathMap.mem os.source_path payload
          then
            let () = notify os.source_path in
            let resolve_behavior history =
              let m = resolution_mapper StrMap.empty history in
              let map_behavior = m.map_behavior m in
              map_behavior
            in
            let resolve_annotation history = function
                None -> None
              | Some m ->
                let mod_nested = norm_annotation history m.modifications in
                if mod_nested = StrMap.empty then None else Some {mod_nested; mod_default=None; mod_kind=CK_BuiltinClass}
            in
            let {annotated_elem; annotation} = PathMap.find os.source_path payload in
            (resolve_behavior current_class annotated_elem, resolve_annotation current_class annotation)
          else
            (os.behavior, os.annotation)
        in

        let current_stmts = if PathMap.mem os.source_path strat_stmts then PathMap.find os.source_path strat_stmts else [] in                
        let pub_state = {
          notify;
          strat_stmts ;
          current_stmts;
          payload;
          current_class }
        in
        let s = impl_mapper pub_state in
        let public = s.map_elements_struct s os.public in
        
        let ppath = DQ.snoc os.source_path `Protected in
        let current_stmts = if PathMap.mem ppath strat_stmts then PathMap.find ppath strat_stmts else [] in        
        let s = impl_mapper {pub_state with current_stmts} in
        let protected = s.map_elements_struct s os.protected in
        {os with public; protected; behavior; annotation}
      );

    map_elements_struct = (fun self {class_members; super; fields} ->
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
            let current_path = DQ.snoc (current_class.tip.clbdy.source_path) (`ClassMember name) in            
            let stmts = if PathMap.mem current_path strat_stmts then PathMap.find current_path strat_stmts else [] in
            
            normalize_classmod_stmts current_class (`ClassMember name) {class_;class_mod} stmts
        in
            
        let class_members = StrMap.mapi map_cm class_members in
        
        (* normalize and attach statements to fields *)
        normalize_stmts current_class {super;fields;class_members} current_stmts
      );
  }

let norm lib notify payload strat_stmts =
  let m = impl_mapper {notify; strat_stmts; payload; current_stmts = []; current_class = (state_of_lib lib).self} in
  m.map_elements_struct m lib
                                      
