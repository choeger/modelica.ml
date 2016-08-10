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

(** Normalization of classLang expressions *)

open Batteries
open Utils
open Location
open Report

module Inter = ModlibInter
module Normalized = ModlibNormalized
module Lookup = ModlibLookup
module Compress = ModlibCompress
module Trans = ModlibTrans
module Deps = ModlibInterDeps
open Inter
open Syntax
open Normalized
open Lookup
open Compress
open Deps

exception NonLeafRecursion
exception Stratification of Path.t * string

(** 
   A stratification result holds the last valid context of the existing prefix and the non existing suffix of the stratified path 
*)
type stratification_result = { lookup_result : lookup_state; protected : bool ; new_element : Path.elem_t } [@@deriving show]
     
(** The target of a stratified path *)
let target { lookup_result; protected; new_element} =
  let parent =
  if protected then
    (Path.snoc lookup_result.current_path `Protected)
  else
    lookup_result.current_path
  in
  Path.snoc parent new_element

let relative p1 p2 =
  let rec eat_prefix p1 p2 = match (Path.front p1,Path.front p2) with
      Some(x,xs),Some(y,ys) when x = y -> eat_prefix xs ys
    | _ -> (Name.of_ptr p1, Name.of_ptr p2)
  in
  let (p1,p2) = eat_prefix p1 p2 in
  {upref=Name.size p1; base=false; downref=p2}

let rec stratify state next todo = match next with
    (`ClassMember _ | `FieldType _ | `SuperClass _ | `Protected) as k ->
    begin match DQ.front todo with
        Some (x, xs) -> next_fwd state (DQ.singleton (k :> Path.elem_t)) x xs
      | None -> {lookup_result=state; protected=false; new_element = k}
    end
  | `Any x ->
    match lookup_continue state {subscripts=[]; ident={txt=x;loc=Location.none}} [] with
      Success {lookup_success_state={current_path}} ->
      begin match DQ.rear current_path with
          None -> raise (IllegalPath "Found value with empty path.")
        | Some(cs,c) ->
          begin match DQ.front todo with
              None ->
              (* This is the newly modified value *)
              {lookup_result=state; protected=false; new_element=c}
            | Some (y, ys) ->
              (* This is an intermediate modified value, must exist locally *)
              if (not (Path.equal cs state.current_path)) then
              assert (Path.equal cs state.current_path) ;
              next_fwd state (DQ.singleton c) y ys
          end
      end
    | Error _ -> raise (Stratification (state.current_path, x))

and next_fwd state fwd next todo = match next with
    `Any x -> stratify (forward_state state fwd) (`Any x) todo
  | (`ClassMember _ | `FieldType _ | `SuperClass _ | `Protected) as k ->
    begin match DQ.front todo with
        Some (x, xs) -> next_fwd state (DQ.snoc fwd (k :> Path.elem_t)) x xs
      | None ->
        begin match DQ.rear fwd with          
            Some(fwd, `Protected) -> 
            {lookup_result=forward_state state fwd; protected=true; new_element = (k :> Path.elem_t)}
          | _ -> 
            {lookup_result=forward_state state fwd; protected=false; new_element = (k :> Path.elem_t)}
        end
    end

let stratify_ptr ptr =
  Report.do_ ;
  o <-- output ;
  match DQ.front ptr with None -> raise EmptyName | Some(x,xs) ->
  try return (stratify (state_of_lib o) x xs) with
  | Stratification (found, not_found) ->
    Report.do_ ;
    log{level=Error;where=none;what=Printf.sprintf "Stratification error: No element %s in %s" not_found (show_class_path found)}; fail

let set_value n = {Normalized.identity_mapper with map_class_value = fun _ _ -> n}

let set_super shape cv = {Normalized.identity_mapper with map_class_value = (fun _ _ -> cv) ;
                                                          map_super_shape = (fun _ _ -> shape)}

let rec shapeof lhs = function
  | Int | Bool | Real | String | Unit | ProtoExternalObject -> Primitive
  | Enumeration ids -> Shape (StrSet.mkmap (fun k -> Syntax.CK_BuiltinAttr) ids)
  | Class os ->
    let pub_cls =
        StrMap.fold (fun k _ s -> StrMap.add k Syntax.CK_Class s) os.public.class_members StrMap.empty in
    let pub_flds = 
        StrMap.fold (fun k v s -> StrMap.add k (Syntax.ck_of_var (flat v.field_class).flat_attr.fa_var) s) os.public.fields pub_cls in
    let prot_cls =
        StrMap.fold (fun k _ s -> StrMap.add k Syntax.CK_Class s) os.protected.class_members pub_flds in
    let prot_flds =
        StrMap.fold (fun k v s -> StrMap.add k (Syntax.ck_of_var (flat v.field_class).flat_attr.fa_var) s) os.protected.fields prot_cls in    
    let pub_shape = IntMap.fold (fun k v s -> match v.super_shape with Shape s' -> StrMap.union s' s | Primitive -> s) os.public.super prot_flds in
    let prot_shape = IntMap.fold (fun k v s -> match v.super_shape with Shape s' -> StrMap.union s' s | Primitive -> s) os.protected.super pub_shape in
    Shape prot_shape
  | Constr {arg} -> shapeof lhs arg
  | Replaceable arg -> shapeof lhs arg
  | cv ->
    match get_class_element lhs.lookup_result lhs.new_element cv [] with
      Success {lookup_success_value} ->
      let shape = shapeof lhs (class_value_of_lookup lookup_success_value) in
      shape
    | Error {lookup_error_todo=todo} ->
      raise (Failure ("Error determining shape: " ^ (Path.show (target lhs)) ^ " - " ^ (Syntax.show_components todo) ^ " == " ^ (show_class_value cv))) (* TODO: log/report error *)

let dynref_found {lookup_success_state={current_ref}} =
  let downref = DQ.map (fun {Syntax.component} -> component.ident.txt) current_ref.known_components in
  if downref = DQ.empty && current_ref.scope = 0 then
    raise (Failure "Did not expect this-reference!") ;
  
  DynamicReference {upref=current_ref.scope; base=false; downref}

let rec norm lhs =
  let open Normalized in

  function
    Empty {class_sort; class_name} -> (if DQ.is_empty class_name then BatLog.logf "Empty class name for %s!\n" (Path.show (target lhs)) else ()) ;
    Report.do_ ;
    return (Class {empty_object_struct with object_sort = class_sort ; source_path = target lhs})

  | Close public_defs ->
    Report.do_ ; o <-- output ;
    begin match lookup_path_direct o (target lhs) with
        `Found {found_value} ->
        let f = flat found_value in
        begin match f.flat_val with
          | Class os ->
            let fields =
              List.fold_left (fun flds {fld_name;fld_pos;fld_defined} ->
                  StrMap.modify fld_name (fun f -> {f with field_pos = fld_pos; field_def = fld_defined}) flds)
                os.public.fields public_defs
            in
            let flat_val = Class {os with public = {os.public with fields}} in
            return (unflat {f with flat_val})
          | _ -> return (unflat f) 
        end    
      | `NothingFound | `PrefixFound _ as result ->
        BatLog.logf "Could not find closed scope\n";
        fail_unresolved {searching=Name.of_ptr lhs.lookup_result.current_path; result}
    end

  | RedeclareExtends ->
    (* self is the class containing the virtual extends statement *)
    let redeclared = lhs.lookup_result.self in
    begin match redeclared.up with
        Some(parent) ->
        (* parent is enclosing class containing the replaceable *)
        let x = match DQ.rear redeclared.tip.clbdy.source_path with
            Some(_,(`ClassMember x | `FieldType x)) -> x
          | _ -> raise Syntax.AstInvariant
        in
            
        (* Go back in scope *)
        let state = state_of_self parent in
            
        (* Create a virtual lookup target by removing all elements *)
        let base_only = {parent.tip.clbdy with public = {empty_elements with super = parent.tip.clbdy.public.super};
                                               protected = {empty_elements with super = parent.tip.clbdy.protected.super}} in
        begin
          match get_class_element_os state base_only {ident={txt=x; loc=Location.none};subscripts=[]} [] with
            Success succ -> return (DynamicReference {upref=1; base=true; downref=Name.of_list [x]})
                                                    
          | Error result ->
            Report.do_ ;
            log{where=none;level=Error;
                what=Printf.sprintf "Could not find redeclared base class %s\n" x};
            fail_lookup result
        end
      | None -> BatLog.logf "Illegal redeclare extends: No enclosing class found."; fail
    end

  | RootReference r ->
    Report.do_ ;
    global <-- output ;
    let name = List.map (fun ident -> {Syntax.ident;subscripts=[]}) r in
    let la = lookup global name in
    begin match la with
        Success {lookup_success_state={current_path}} ->
        return (GlobalReference current_path)
      | Error err -> fail_lookup err 
    end

  | KnownPtr p ->
    Report.do_ ;    
    strat <-- stratify_ptr p ;
    let dr = DynamicReference (relative lhs.lookup_result.current_path (target strat)) in
    return (dr)

  | Reference n ->
    let components = List.map (fun ident -> {Syntax.ident;subscripts=[]}) n in
    begin match components with
        x::xs ->
        begin match lookup_lexical_in lhs.lookup_result x xs with
            Success succ -> return (dynref_found succ)
          | Error err ->            
            fail_lookup err
      end
    | [] -> raise EmptyName
    end
  | Constr {constr=CRepl; arg} -> Report.do_ ;
    argv <-- norm lhs arg ;
    return (Replaceable argv) 

  | Constr {constr; arg} -> Report.do_ ;
    argv <-- norm lhs arg ;
    begin match argv with
        Replaceable arg -> return (Replaceable (Constr {arg;constr=norm_constr constr})) 
      | arg -> return (Constr {arg; constr = norm_constr constr})
    end

  | PInt -> return Int
  | PBool -> return Bool
  | PReal -> return Real
  | PString -> return String
  | PExternalObject -> return ProtoExternalObject
  | PEnumeration ids -> return (Enumeration ids)

exception Check

let rec check = function
    Class os -> if os.source_path = empty_object_struct.source_path then raise Check else
      begin
        el_check os.public ;
        el_check os.protected
      end
  | Constr {arg} -> check arg
  | _ -> ()               

and el_check {class_members} = StrMap.iter (fun k v -> check v.class_) class_members

let rec norm_prog i p =
  Report.do_ ;
  o <-- output;
  if i >= Array.length p then return o
  else
    let {lhs=ptr;rhs} = p.(i) in
    Report.do_ ;
    lhs <-- stratify_ptr ptr ;
    norm <-- norm lhs rhs;
    let patch =
      match lhs.new_element with
        `SuperClass n ->
        set_super (shapeof lhs norm) norm             
      | _ -> set_value (norm_cv norm)
    in
    let o' = update (target lhs) patch o in
    set_output (o') ;
    norm_prog (i+1) p

open FileSystem

let link_unit linkage {Trans.class_code} = linkage @ class_code

let rec link_package linkage {sub_packages; external_units; package_unit} =
  List.fold_left link_package (List.fold_left link_unit (link_unit linkage package_unit) external_units) sub_packages

let link_root {root_units; root_packages} =
  List.fold_left link_package (List.fold_left link_unit [] root_units) root_packages

let norm_pkg_root root =
  let linkage = link_root root in
  let cc = preprocess linkage in
  Report.do_ ;
  (* normalize signature *)
  o <-- norm_prog 0 cc ;
  (* compress the result *)
  let c = compress_elements o in
  return c



