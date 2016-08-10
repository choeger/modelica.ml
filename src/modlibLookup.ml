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

open Batteries
open Utils
open Location
module Inter = ModlibInter
module Normalized = ModlibNormalized
open Inter
open Syntax
open Syntax_fragments
open Normalized
    
exception EmptyName
exception ExpansionException of string
exception ForwardFailure of Path.elem_t
exception EmptyScopeHistory
exception HierarchyError
exception DecompressionError
  
type trace_t = Path.t DQ.t [@@deriving show,yojson]

type lnode = { up : lnode option; tip : lclass }

and lclass = { clup : lnode option; clbdy : object_struct; }
  [@@deriving show,yojson]

type lookup_value = LClass of lclass | LPrimitive of class_value
  [@@deriving show,yojson]

let class_value_of_lookup = function LClass {clbdy} -> Class clbdy | LPrimitive cv -> cv

let map_lv f = function LClass {clup; clbdy} -> LClass {clup; clbdy}
                      | LPrimitive v -> LPrimitive (f v)

type lookup_state = {
  self : lnode ;
  trace : trace_t; (** The found references *)
  current_ft : StrSet.t ; (** Currently constructed possibly recursive flat types *)
  current_path : Path.t ; (** The path to the current class value *)
  current_attr : flat_attributes ;
  current_ref : Syntax.known_ref; (** The search request as a resolved component *)
} [@@deriving show,yojson]


let rec root_class_of self = match self.up with None -> self.tip | Some self -> root_class_of self

let empty_lookup_state = {trace=DQ.empty; self={up=None;tip={clup=None; clbdy=empty_object_struct}};
                          current_path=Path.empty;
                          current_ft = StrSet.empty;
                          current_attr=no_attributes; current_ref={known_components=DQ.empty; scope=0}}

let dump_lookup_state {current_path} = Printf.sprintf "Last class: %s\n" (Path.show current_path)

type lookup_success_struct = { lookup_success_state : lookup_state ;
                               lookup_success_value : lookup_value ;
                             } [@@deriving show,yojson]

type lookup_error_struct = { lookup_error_state : lookup_state ;
                             lookup_error_todo : component list }
                           [@@deriving show,yojson]

type lookup_result = Success of lookup_success_struct 
                   | Error of lookup_error_struct
  [@@deriving show,yojson]


(** wrap a scope of visited classes into a new lookup state *)
let state_of_self self = {empty_lookup_state with
                          self;
                          current_path = self.tip.clbdy.source_path}

let undefined x {Normalized.class_members; super; fields} =
  let not_inherited _ v b = b && (match v.super_shape with Shape flds -> not (StrMap.mem x flds) | _ -> true) in
  not (StrMap.mem x class_members) && not (StrMap.mem x fields) && (IntMap.fold not_inherited super true)

let rec get_class_element_in state {Normalized.class_members; super; fields} x xs =  
  if StrMap.mem x.ident.txt class_members then begin
    let fa = flat (StrMap.find x.ident.txt class_members).class_ in
    let current_ref = {state.current_ref with known_components =
                                                DQ.snoc state.current_ref.known_components {kind=CK_Class; known_type=None; component=x}} in
    get_class_element {state with current_ref} (`ClassMember x.ident.txt) (unflat fa) xs
  end
  else if StrMap.mem x.ident.txt fields then begin
    let fa = flat (StrMap.find x.ident.txt fields).field_class in
    let known_type = ft_of_cv_safe state fa.flat_val in
    let kind = ck_of_var fa.flat_attr.fa_var in
    let known_components = DQ.snoc state.current_ref.known_components {Syntax.kind; component=x; known_type} in
    let current_ref = {state.current_ref with known_components} in
    get_class_element {state with current_ref; current_attr=fa.flat_attr} (`FieldType x.ident.txt) fa.flat_val xs
  end
  else begin
    (pickfirst_class state x xs (IntMap.bindings super) )
  end
  
and get_class_element_os state {public;protected} x xs =
  let f = get_class_element_in state public x xs in
  match f with
    Error {lookup_error_state={current_ref}} when undefined x.ident.txt public ->
    (* Nothing found, search protected section *)
    let current_path = DQ.snoc state.current_path `Protected in
    get_class_element_in {state with current_path} protected x xs
  | _ as r -> r (* Something found *)

and pickfirst_class state x xs = function
    [] -> Error {lookup_error_state=state; lookup_error_todo=x::xs}
  | (k,v)::vs ->
    begin
      match v.super_shape with
      | Primitive ->
        let current_ref = {state.current_ref with known_components =
                                                    DQ.append state.current_ref.known_components
                                                      (DQ.of_list (List.map (fun component -> {kind=CK_BuiltinAttr;component;known_type=None}) (x::xs)))
                          } in
        Success {lookup_success_state={state with current_ref}; lookup_success_value=LPrimitive Unit}
      | Shape shape when StrMap.mem x.ident.txt shape ->
        (* Always re-evaluate the super class to catch all redeclarations *)
        let super = get_class_element state (`SuperClass k) v.super_type [] in
        begin match super with
          | Success {lookup_success_state; lookup_success_value=LClass {clup;clbdy}} ->
            let super_state = {state with self={state.self with up=clup};
                                          current_path = DQ.snoc state.current_path (`SuperClass k);
                              } in
            get_class_element_os super_state clbdy x xs
            
        | Success {lookup_success_state; lookup_success_value} ->
            raise (Failure ("Lookup of " ^ x.ident.txt ^ "in a non-structured type"))
        | (Error _ ) as e -> e
        end
      | Shape s ->
        pickfirst_class state x xs vs
    end

(**
  $state : lookup state 
  $k : kind of this class value
  $p : components todo
*)
and get_class_element state k e p =  
  let open Normalized in  
  let current_path = Path.snoc state.current_path k in
  let state = {state with current_path} in  
  eval state p e

and project state v = function
      [] ->
      let open Flags in
      begin match v with
          LClass {clbdy={object_sort=Record|OperatorRecord|Function|OperatorFunction} as os} ->
          (* patch correct type and kind for records and functions 
             This is necessary here, since we need to be "inside" the function/record
             (from a lookup state perspective) to resolve the declarations of
             all public components.
          *)
          let current_ref = match DQ.rear state.current_ref.known_components with
              None ->
              (* We cannot patch what is not there (i.e. a superclass function) *)
              state.current_ref
                
            | Some(xs, x) ->
              let known_type = ft_of_cv_safe state (Class os) in
              let kind = match os.object_sort with Function|OperatorFunction -> CK_Function | _ -> x.kind in
              let known_components = DQ.snoc xs {x with kind; known_type} in
              {state.current_ref with known_components}
          in
          let state = {state with current_ref} in
          Success {lookup_success_state=state;lookup_success_value=v}
        | _ ->
          let lookup_success_value = map_lv (fun sval ->
              let {flat_attr; flat_val} = extract_attributes state.current_attr sval in
              unflat {flat_val;flat_attr}) v       
          in
          Success {lookup_success_state=state;lookup_success_value}
      end
    | x::xs ->      
      begin match v with
          LClass {clbdy} ->
          get_class_element_os {state with current_attr = no_attributes} clbdy x xs                              
        | LPrimitive cv ->
          let {flat_val; flat_attr} as flat = extract_attributes state.current_attr cv in

          let is_attr = function
              {ident={txt="start" | "min" | "max" | "fixed" | "quantity" | "stateSelect" | "nominal" | "unit" | "displayUnit"}} -> true
            | _ -> false
          in

          let cv_of_attr p = function
              {ident={txt="start" | "min" | "max" | "nominal"}} -> p
            | {ident={txt="quantity" | "unit" | "displayUnit"}} -> Normalized.String
            | {ident={txt="stateSelect"}} -> Enumeration (StrSet.of_list ["never";"avoid";"default";"prefer";"always"])
            | {ident={txt="fixed"}} -> Bool
            | {ident={txt}} -> raise (Failure (txt ^ " is not a valid attribute"))
          in
          
          begin match flat_val with
            | Int | Real | String | Bool ->
              begin match xs with
                  [] when is_attr x ->
                  let attr_cv = cv_of_attr flat_val x in
                  let known_type = ft_of_cv_safe state attr_cv in
                  let attr = {kind=CK_BuiltinAttr; component=x; known_type} in
                  let lookup_success_state =
                    {state with current_ref =
                                  {state.current_ref with known_components =
                                                            DQ.snoc state.current_ref.known_components attr}} in
                  Success {lookup_success_state;
                           lookup_success_value=LPrimitive attr_cv}
                | _ -> Error {lookup_error_todo=(x::xs); lookup_error_state=state}
              end
            | Enumeration flds ->
              begin match xs with                         
                | [] when is_attr x ->
                  let attr_cv = cv_of_attr flat_val x in
                  let known_type = ft_of_cv_safe state attr_cv in
                  let attr = {kind=CK_BuiltinAttr; component=x; known_type} in
                  let lookup_success_state =
                    {state with current_ref = {state.current_ref with known_components =
                                                                        DQ.snoc state.current_ref.known_components attr}} in
                  Success {lookup_success_state;
                           lookup_success_value=LPrimitive attr_cv} 
                
                | [] when StrSet.mem x.ident.txt flds ->
                  let lookup_success_state =
                    let known_type = ft_of_cv_safe state flat_val in
                    let known_components = DQ.snoc state.current_ref.known_components {kind=CK_BuiltinAttr; component=x; known_type} in
                    {state with current_ref = {state.current_ref with known_components}} in
                  Success {lookup_success_state;
                           lookup_success_value=LPrimitive (unflat flat)}

                | _ -> Error {lookup_error_todo=(x::xs); lookup_error_state=state}
              end
            | v -> raise (Failure ("Such builtins should not occur here (" ^ x.ident.txt ^ ": " ^ (show_class_value v) ^ ")") )
          end
      end

and eval state p = function
  | Class os ->
    assert (not (Path.equal os.source_path state.self.tip.clbdy.source_path)) ;
    let tip = {clup = Some state.self; clbdy = os} in
    let self =  {up = tip.clup; tip} in
    let lv = LClass tip in    
    project {state with self} lv p

    (* follow dynamic references through self to implement redeclarations *)
  | DynamicReference {upref; base; downref} ->
    let rec upwards self = function
        0 -> {self with up = self.tip.clup}
      | n -> begin match self.up with None -> raise HierarchyError
                                    | Some up -> upwards up (n-1)
        end
    in    
    let self = upwards state.self upref in
    let state = {state with self} in
    begin match DQ.front downref with
        None ->
        project state (LClass self.tip) p
      | Some (y,_) when base ->
        (* TODO: assert rest is empty *)

        (* Find the superclass of the inherited field *)
        let find_y _ super = match super.super_shape with
            Shape s -> StrMap.mem y s
          | _ -> false
        in
        let pubf = IntMap.filter find_y self.tip.clbdy.public.super in
        let protf = IntMap.filter find_y self.tip.clbdy.protected.super in
        let (k, v) =
        if IntMap.is_empty pubf then
          if IntMap.is_empty protf then
            raise (Failure ("Redeclare extends not inherited"))
          else
            IntMap.choose protf
        else
          IntMap.choose pubf
        in
        let super = get_class_element state (`SuperClass k) v.super_type [] in
        begin match super with
          | Success success ->
            (* Continue search *)
            let  {self; current_attr} = success.lookup_success_state in
            begin match project {state with self; current_attr} success.lookup_success_value [any y] with
              | Success {lookup_success_state; lookup_success_value=LClass {clup;clbdy}} ->
                let super_state = {state with self={state.self with up=clup};
                                              current_path = DQ.snoc state.current_path (`SuperClass k);
                                  } in
                project super_state (LClass {clup;clbdy}) p
            
              | Success {lookup_success_state; lookup_success_value} ->
                raise (Failure ("Lookup of " ^ y ^ "in a non-structured type"))

              | Error e -> Error e
            end
          | e -> e
        end
      | Some (y,ys) ->
        begin
          (* Evaluate dynamic reference: back to tip, open recursion *)
          match get_class_element_os
                  state state.self.tip.clbdy (any y) (List.map any (Name.to_list ys)) with
            Success success ->
            (* Continue search *)
            let  {self; current_attr} = success.lookup_success_state in
            project {state with self; current_attr} success.lookup_success_value p
          | e -> e
        end
    end

  | GlobalReference g ->
    begin match Name.front (Name.of_ptr g) with
      Some(x,xs) ->
        let root = root_class_of state.self in
        let state = {state with self={up=None; tip=root}} in
        begin match get_class_element_os state root.clbdy (any x) (List.map any (Name.to_list xs)) with
        Success success ->
            (* Continue search *)
            project {state with self = success.lookup_success_state.self} success.lookup_success_value p
          | e -> e
        end
      | None -> raise EmptyName
    end
    
  (* Replaceable/Constr means to look into it *)
  | Replaceable v ->
    eval {state with current_attr = {state.current_attr with fa_replaceable=true}} p v
  | Constr {constr=Cau c; arg} ->
    eval {state with current_attr = {state.current_attr with fa_cau = Some c}} p arg
  | Constr {constr=Con c; arg} ->
    eval {state with current_attr = {state.current_attr with fa_con = Some c}} p arg
  | Constr {constr=Var v; arg} ->
    eval {state with current_attr = {state.current_attr with fa_var = Some v}} p arg
  | Constr {constr=Sort s; arg} ->
    eval {state with current_attr = {state.current_attr with fa_sort = Some s}} p arg
                                     
  | v -> project state (LPrimitive v) p

(** Start lookup with the given state *)
and lookup_continue state x xs =
  get_class_element_os state state.self.tip.clbdy x xs

and lookup_continue_or_yield state = function
    [] ->
    Success {lookup_success_state=state; lookup_success_value=LClass state.self.tip}
    | x::xs -> lookup_continue state x xs

and arg_of_field state (x, {field_class;field_def}) =
  let ({flat_attr;flat_val}, ftarg_type) =
      match lookup_continue state {ident=nl x; subscripts=[]} [] with
        Success {lookup_success_value=lv; lookup_success_state=state'} ->
        let v = class_value_of_lookup lv in
        let ft = extract_attributes state'.current_attr v in
        let ftarg_type=ft_of_cv state' ft.flat_val in
        (ft, ftarg_type)        
      | _ ->
        BatLog.logf "Could not resolve function component %s\n" x ;
        raise NotFlat
  in  
  (flat_attr, {ftarg_name=x; ftarg_type; ftarg_opt=field_def})
    
and fun_of_cv state fields =
  let split (inputs,outputs) (x, field) =
    let ({fa_cau},arg) = arg_of_field state (x,field) in
    match fa_cau with
      Some Flags.Input -> (arg :: inputs, outputs)
    | Some Flags.Output -> (inputs, arg.ftarg_type::outputs)
    | _ -> (inputs, outputs)
  in
  let (inputs, outputs) = List.fold_left split ([], []) (fields_in_order fields) in
  FTFunction (inputs, outputs)

and ft_of_field state {field_class} =
  ft_of_cv state field_class

and or_of_cv state or_tag {fields;class_members;super} =
  let operator sym =
    match get_class_element_in state {fields; class_members; super} {ident=nl sym; subscripts=[]} [] with
      Success {lookup_success_value=lv; lookup_success_state=op_state} ->
      let {flat_attr;flat_val} = flat (class_value_of_lookup lv) in
      begin match flat_attr.fa_sort with
          Some Flags.Operator ->
          (* In case of an operator, collect all functions in this operator *)
          begin match flat_val with
              Class os ->
              (* TODO: protected?? *)
              let keys = StrMap.keys os.public.class_members in
              let add_operator ops opname = match get_class_element_in op_state os.public {ident=nl opname;subscripts=[]} [] with
                  Success {lookup_success_state={current_ref}} ->
                  begin 
                    match ft_of_kcs current_ref.known_components with
                      Some FTFunction (opargs, _) -> {opargs; opname}::ops
                    | _ -> ops
                  end
                | _ -> ops
              in
              Enum.fold add_operator [] keys 
            | _ -> []
          end
        | Some Flags.OperatorFunction ->
          begin match ft_of_kcs op_state.current_ref.known_components with
              Some FTFunction (opargs, _) -> [{opargs; opname="default"}]
            | _ -> []
          end
        | _ -> []
      end
    | _ -> []
  in
  let or_fields = List.map (fun fld -> snd (arg_of_field state fld)) (fields_in_order fields) in
  let or_zero = operator "'0'" in
  let or_constructor = operator "'constructor'" in
  let or_string  = operator "'String'" in
  let or_plus  = operator "'+'" in
  let or_minus  = operator "'-'" in
  let or_mult  = operator "'*'" in
  let or_div  = operator "'/'" in
  let or_pow  = operator "'^'" in
  let or_eq  = operator "'=='" in
  let or_neq  = operator "'<>'" in
  let or_gt  = operator "'>'" in
  let or_lt  = operator "'<'" in
  let or_geq  = operator "'>='" in
  let or_leq  = operator "'<='" in
  let or_and  = operator "'and'" in
  let or_or = operator "'or'" in
  let or_not = operator "'not'" in

  {or_tag; or_fields;
   or_constructor;
   or_zero;
   or_string;
   or_plus ;
   or_minus ;
   or_mult ;
   or_div ;
   or_pow ;
   or_eq ;
   or_neq ;
   or_gt ;
   or_lt ;
   or_geq ;
   or_leq ;
   or_and ;
   or_not ;
   or_or }
  
and ft_of_cv state = function
    Int ->  FTInteger
  | Real -> FTReal
  | String -> FTString    
  | Bool -> FTBool
  | Unit | ProtoExternalObject -> FTObject []
  | Enumeration s -> FTEnum s
  | Constr {arg; constr=Array n} -> FTArray (ft_of_cv state arg, n)
  | Constr {arg} -> ft_of_cv state arg
  | Replaceable cv -> ft_of_cv state cv
  | Class {object_sort=Flags.Function; public={fields}; source_path} ->
    fun_of_cv state fields
      
  | Class {source_path; object_sort = Flags.OperatorRecord; public} ->
    let or_tag = Pprint_modelica.expr2str (cre (UnknownRef {root=true; components=List.map any (Name.to_list (Name.of_ptr source_path))})) in    
    if StrSet.mem or_tag state.current_ft then
      FTOperatorRecordSelf or_tag
    else begin
      let state = {state with current_ft = StrSet.add or_tag state.current_ft} in
      FTOperatorRecord (or_of_cv state or_tag public)
    end

  | Class {public={fields}} ->
    FTObject (List.map (fun fld -> snd (arg_of_field state fld)) (fields_in_order fields))
      
  | e ->
    begin match eval state [] e with
        Success ls ->
        ft_of_cv ls.lookup_success_state
          (class_value_of_lookup ls.lookup_success_value)        
      | _ -> raise NotFlat
    end
      
and ft_of_cv_safe state cv =
  try Some (ft_of_cv state cv) with
  | NotFlat -> None


let rec forward state k c (todo:Path.t) =
  let current_path = DQ.snoc state.current_path (k :> Path.elem_t) in
  let state = {state with current_path} in
  match c with
  (* always append history, even if todo is empty *)
    (Replaceable (Class os) | Class (os)) ->
    let self = {tip = {clup=Some state.self; clbdy=os}; up=Some state.self} in
    forward_os {state with self} os todo
  | c -> begin
      match DQ.front todo with
      | None -> state
      | Some(x,xs) ->
        raise (ExpansionException ("expected a class. got: " ^ (show_class_value c)))
    end

and forward_os state {public;protected} todo =
  match DQ.front todo with
    None -> state
  | Some(`Protected, xs) -> forward_elements
                              {state with current_path = Path.snoc state.current_path `Protected} protected xs
  | _ -> forward_elements state public todo

and forward_elements state {class_members; super; fields} (todo:Path.t) =
  match DQ.front todo with
  | None -> raise (ExpansionException "Unexpected end-of-path")
  | Some(`FieldType x, xs) when StrMap.mem x fields ->
    forward state (`FieldType x) (StrMap.find x fields).field_class xs
      
  | Some(`ClassMember x, xs) when StrMap.mem x class_members ->
    forward state (`ClassMember x) (StrMap.find x class_members).class_ xs
      
  | Some(`SuperClass i, xs) when IntMap.mem i super ->
    raise (ExpansionException ("Cannot forward into a superclass: " ^ (Path.show state.current_path)))

  | Some (`Protected, xs) -> raise (IllegalPath "protected")

  | Some (x, _) ->
    BatLog.logf "Fowarding failed. No element %s in %s" (Path.show_elem_t x) (Path.show state.current_path) ;
    raise (ForwardFailure x)

(** Forward a lookup state by an (existing) (relative) pointer *)
let forward_state state todo = 
  forward_os state state.self.tip.clbdy todo

(** Start lookup with the given state, follow lexical scoping rules *)
let rec lookup_lexical_in state x xs =
  if undefined x.ident.txt state.self.tip.clbdy.public &&
     undefined x.ident.txt state.self.tip.clbdy.protected then
    (* Found nothing, climb up scope *)
    begin
      match state.self.up with
        None -> Error {lookup_error_state=state; lookup_error_todo=x::xs}
      | Some self -> lookup_lexical_in {state with self;current_ref={state.current_ref with scope = state.current_ref.scope +1} } x xs
    end
  else begin
    get_class_element_os state state.self.tip.clbdy x xs
  end
(** Create a lookup state from a normalized signature (i.e. root class) *)
let state_of_lib lib =
  {empty_lookup_state with
    self={tip={clup=None; clbdy={empty_object_struct with public=lib}};up=None}}

let lookup o p =
  let open Normalized in
  let state = state_of_lib o in
  match p with
    [] -> Success {lookup_success_value = LClass state.self.tip;
                   lookup_success_state = state} ;
  | x::xs ->    
    lookup_lexical_in state x xs

