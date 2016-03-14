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

type payload_stmts = Syntax.behavior PathMap.t

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

  (* 10.3.5 Matrix and Vector Algebra Functions *)
  | "transpose" | "outerProduct" | "symmetric" | "cross" | "skew"
    -> builtin CK_BuiltinFunction

  (* Special, see 3.7.2 *)
  | "delay" | "cardinality" | "homotopy" | "semiLinear" 
  | "inStream" | "actualStream" | "spatialDistribution"
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
  | "String" | "StateSelect" | "Connections" | "AssertionLevel" -> builtin CK_BuiltinClass

  | _ -> BatLog.logf "Error searching for %s\n" first.ident.txt ; raise (NoSuchClass first.ident)

exception ResolutionError of lookup_error_struct

let rec resolve_env env self first rest =
  if StrMap.mem first.ident.txt env then
    (false, DQ.cons {kind=CK_LocalVar; component=first} (DQ.of_list (List.map (fun component -> {kind=CK_VarAttr; component}) rest)))
  else
    let state = state_of_self self in
    match lookup_lexical_in state first rest with
      Success {lookup_success_state={current_ref;current_scope=0}} -> (false, current_ref)
    | Success {lookup_success_state={current_ref;current_scope=up}} ->
      (* At this point, our lookup history is purely lexical, we can directly drop the surrounding classes *)
      (* TODO: encode this assertion as an OCaml type *)
      let rec class_name_of_path name p = match DQ.rear p with
        | None -> name 
        | Some(xs, `ClassMember txt) -> class_name_of_path (DQ.cons {kind=CK_Class; component={ident={txt;loc=Location.none}; subscripts=[]}} name) xs
        | Some(xs, `Protected) -> class_name_of_path name xs
        | _ -> raise (Failure "History not lexical?")
      in
        
      let rec upwards self up =
        match self.up with None -> if up = 0 then DQ.empty else raise HierarchyError
                         | Some self' ->
                           if (up = 0) then class_name_of_path current_ref self.tip.clbdy.source_path
                           else upwards self' (up-1)
      in
        
      (true, upwards self up)

    | Error {lookup_error_state={self={up=None}}} ->
      (true, resolve_builtin first rest)

    | Error {lookup_error_todo=x::_} ->
      BatLog.logf "No field %s in %s.\n" x.ident.txt (show_object_struct self.tip.clbdy) ;
      raise (NoSuchField x.ident)
    | Error _ -> raise (Failure "Lookup failed with empty todo...")
    
let resolve_ur env self {root;components} =
  match components with
    cmp :: components ->
    if root then
      let (_, cs) = resolve_env StrMap.empty {tip=root_class_of self;up=None} cmp components in
      RootRef cs
    else begin
      match resolve_env env self cmp components with
        (false,cs) -> KnownRef cs
      | (true,cs) -> RootRef cs
    end
  | [] -> raise AstInvariant

let add_idx env idx = 
  let mk_env = fun {variable={txt};range} m -> StrMap.add txt range env in
  List.fold_right mk_env idx env


let rec resolution_mapper env history = { Syntax.identity_mapper with
                                          on_component_reference = {
                                            Syntax.identity_mapper.on_component_reference with
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

let resolve_behavior history =
  let m = resolution_mapper StrMap.empty history in
  m.map_behavior m

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

exception ModificationTargetNotFound of components

(* Normalize all statements in a direct class modification *)
let rec normalize_classmod_stmts self kind {class_; class_mod} =
  function
  | [] -> {class_; class_mod}
  | {field_name=[]}::_ -> raise (Failure "empty modification on class")
  | {field_name; exp}::stmts ->
    (* normalize the modified component *)
    let field_name = match get_class_element (state_of_self self) kind class_  field_name with
        Success {lookup_success_state={current_ref}} -> current_ref
      | Error {lookup_error_todo=todo} | Recursion {lookup_recursion_todo=todo} ->
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
          begin match Path.front current_ref with
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
          begin match Path.front current_ref with
            | Some({kind=CK_Class},_) -> raise (Failure "Expected to modify a component")

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
          begin match Path.front current_ref with
              Some(y,ys) ->
              let {super_mod} as sc = IntMap.find n super in
              let super_mod = merge_mod exp y ys super_mod in
              normalize_stmts self {es with super = IntMap.add n {sc with super_mod} super} stmts
          end
      end
    | Error {lookup_error_todo=todo} | Recursion {lookup_recursion_todo=todo} ->
      let () = BatLog.logf "Error looking up modification target %s\n" (show_components todo) in
      raise (ModificationTargetNotFound todo)


let rec impl_mapper {notify; strat_stmts; payload; current_class; current_stmts} =
  let class_name path = DQ.of_enum (Enum.filter_map (function `ClassMember x -> Some {kind=CK_Class;component={ident={txt=x;loc=Location.none};subscripts=[]}} | _ -> None) (DQ.enum path)) in
  
  { ModlibNormalized.identity_mapper with
    
    map_object_struct = (fun self os ->
        (* Update the lookup environment *)
        let current_class = {tip={clup=Some current_class; clbdy=os}; up=Some current_class}          
        in
        let behavior =
          if PathMap.mem os.source_path payload
          then
            let () = notify os.source_path in
            resolve_behavior current_class (PathMap.find os.source_path payload)
          else
            os.behavior
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
        {os with public; protected; behavior}
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
                                      
