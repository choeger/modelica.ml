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
                    current_stmts : strat_stmt list ; current_classes : history_t }

exception NoSuchField of str
exception DoubleModification of str
exception AstInvariant
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
  | "cat" | "zeros" | "fill" | "ones" | "identity" | "diagonal" -> builtin CK_BuiltinFunction

  (* Builtin Classes *)
  | "String" | "StateSelect" | "Connections" -> builtin CK_BuiltinClass

  | _ -> BatLog.logf "Error searching for %s\n" first.ident.txt ; raise (NoSuchClass first.ident)

exception ResolutionError of lookup_error_struct

let rec resolve_env env history first rest =
  if StrMap.mem first.ident.txt env then  
    DQ.cons {kind=CK_LocalVar; component=first} (DQ.of_list (List.map (fun component -> {kind=CK_VarAttr; component}) rest))
  else
    let state = {history ;
                 trace = DQ.empty ;
                 current_ref = DQ.empty;
                 current_attr = no_attributes;
                 current_path = path_of_history history}
    in
    try 
      match lookup_lexical_in state first rest with
        Success {lookup_success_state={current_ref}} -> current_ref
      | Error err ->
        BatLog.logf "Error looking up %s\nLast scope:%s\n" (Syntax.show_components err.lookup_error_todo) (Path.show err.lookup_error_state.current_path);
        raise (ResolutionError err)
    with
      EmptyScopeHistory -> resolve_builtin first rest
    
let resolve_ur env history {root;components} =
  match components with
    cmp :: components ->
    if root then
      match DQ.front history with
        Some (e, _) ->
        resolve_env StrMap.empty (DQ.singleton e) cmp components
      | None -> raise (Failure "no root class found")
    else
      resolve_env env history cmp components
  | [] -> raise AstInvariant

let add_idx env idx = 
  let mk_env = fun {variable={txt};range} m -> StrMap.add txt range env in
  List.fold_right mk_env idx env


let rec resolution_mapper env history = { Syntax.identity_mapper with
                                          on_component_reference = {
                                            Syntax.identity_mapper.on_component_reference with
                                            map_UnknownRef = (fun _ ur -> KnownRef (resolve_ur env history ur));
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
let rec normalize_classmod_stmts history kind {class_; class_mod} =
  function
  | [] -> {class_; class_mod}
  | {field_name=[]}::_ -> raise (Failure "empty modification on class")
  | {field_name; exp}::stmts ->
    (* normalize the modified component *)
    let field_name = match get_class_element (state_of_history history) kind class_  field_name with
        Success {lookup_success_state={current_ref}} -> current_ref
      | Error {lookup_error_todo=todo} | Recursion {lookup_recursion_todo=todo} ->
        raise (ModificationTargetNotFound todo)
    in
    let exp = resolve StrMap.empty history exp in

    (* merge modification and continue *)
    let class_mod =
    begin match DQ.front field_name with
        None -> raise (Failure "empty modification on class")
      | Some(y,ys) -> merge_mod exp y ys class_mod
    end in
    normalize_classmod_stmts history kind {class_; class_mod} stmts

(* Normalize all statements in the given element structure *)
let rec normalize_stmts history ({super;fields;class_members} as es)=
  function
  | [] -> es
  | {field_name=y::ys;exp}::stmts ->
    (* normalize the modified component *)
    let field_name = resolve_env StrMap.empty history y ys in
    let exp = resolve StrMap.empty history exp in
    
    begin match DQ.front field_name with
      | None -> normalize_stmts history es stmts (* bogus stmt *)                  

      (* TODO: nested modification inside classes *)                 
      
      (* Local field *)
      | Some ({kind=CK_Constant | CK_Continuous | CK_Parameter | CK_Discrete as kind; component},xs) when StrMap.mem component.ident.txt fields ->
        let insert mod_kind fld xs = match DQ.front xs with
            None -> {fld with field_mod = {mod_kind; mod_default=Some exp; mod_nested=fld.field_mod.mod_nested}}
          | Some(y,ys) -> {fld with field_mod = {fld.field_mod with mod_kind; mod_nested = merge_mod exp y ys fld.field_mod.mod_nested}} 
        in

        let fld = StrMap.find component.ident.txt fields in
        let class_field = insert kind fld xs 
        in normalize_stmts history {es with fields = StrMap.add component.ident.txt class_field fields} stmts

      (* Inherited field *)
      | Some ({kind=CK_Constant | CK_Continuous | CK_Parameter | CK_Discrete as kind; component},xs) ->

        (* Search superclasses *)
        let rec modify_super_field history x super =
          (* Get the first inherited class field named x or None *)
          let rec take enum = Enum.get (Enum.filter_map get_fld enum)
          and get_fld ((i, {class_; class_mod}) as s) = match class_ with
              Class os when StrMap.mem x.ident.txt os.public.fields -> Some s
            | Class os when StrMap.mem x.ident.txt os.protected.fields -> Some s
            | Class os ->
              (* Regardless what we found, if we find something yield this superclass *)
              let n = take (Enum.append (IntMap.enum os.public.super) (IntMap.enum os.protected.super)) in
              Option.map (fun _ -> s) n              
            | GlobalReference r ->
              begin
                match DQ.front history with
                  Some (e, _) ->
                  begin match lookup_path_direct e.entry_structure.public r with
                      `Found {found_value} -> get_fld (i, {class_=found_value; class_mod})
                    | _ -> None
                  end
                | None -> raise (Failure "no root class found")
              end
            | _ -> None
          in

          match take (IntMap.enum super) with
            None ->
            BatLog.logf "Internal Error: No field %s after resolution\n" (show_component x) ;
            raise (NoSuchField component.ident) (* Should better not happen *)
          | Some (i, s) -> IntMap.add i {s with class_mod = merge_mod exp {kind;component} xs s.class_mod} super
        in
                
        let super = modify_super_field history component super in
        normalize_stmts history {es with super} stmts

      | Some(x,_) -> raise (Failure ("Don't know how to handle " ^ (show_known_component x)))
    end

let rec impl_mapper {notify; strat_stmts; payload; current_classes; current_stmts} =
  let class_name path = DQ.of_enum (Enum.filter_map (function `ClassMember x -> Some {kind=CK_Class;component={ident={txt=x;loc=Location.none};subscripts=[]}} | _ -> None) (DQ.enum path)) in
  
  { ModlibNormalized.identity_mapper with
    
    map_object_struct = (fun self os ->
        (* Update the lookup environment *)
        let current_classes =
          let entry_kind =
            match DQ.rear os.source_path with
              Some (_, `ClassMember x) -> `ClassMember x
            | _ -> raise (Failure "Implementation normalization on non-lexical class")
          in
          DQ.snoc current_classes {entry_kind; entry_structure = os}
        in
        let behavior =
          if PathMap.mem os.source_path payload
          then
            let () = notify os.source_path in
            resolve_behavior current_classes (PathMap.find os.source_path payload)
          else
            os.behavior
        in

        let current_stmts = if PathMap.mem os.source_path strat_stmts then PathMap.find os.source_path strat_stmts else [] in                
        let pub_state = {
          notify;
          strat_stmts ;
          current_stmts;
          payload;
          current_classes }
        in
        let s = impl_mapper pub_state in
        let public = s.map_elements_struct s os.public in

        let ppath = DQ.snoc os.source_path `Protected in
        let current_stmts = if PathMap.mem ppath strat_stmts then PathMap.find ppath strat_stmts else [] in        
        let s = impl_mapper {pub_state with current_stmts} in
        let protected = s.map_elements_struct s os.protected in
        {os with public; protected; behavior});

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
            let current_path = DQ.snoc (path_of_history current_classes) (`ClassMember name) in            
            let stmts = if PathMap.mem current_path strat_stmts then PathMap.find current_path strat_stmts else [] in
            
            normalize_classmod_stmts current_classes (`ClassMember name) {class_;class_mod} stmts
        in
            
        let class_members = StrMap.mapi map_cm class_members in
        
        (* normalize and attach statements to fields *)
        normalize_stmts current_classes {super;fields;class_members} current_stmts
      );
  }

let norm lib notify payload strat_stmts =
  let m = impl_mapper {notify; strat_stmts; payload; current_stmts = []; current_classes = (state_of_lib lib).history} in
  m.map_elements_struct m lib
                                      
