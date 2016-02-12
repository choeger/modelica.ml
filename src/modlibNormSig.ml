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
open Normalized
open Lookup
open Compress
open Deps

exception NonLeafRecursion
exception Stratification of Path.t * string

(** 
   A stratification result holds the last valid context of the existing prefix and the non existing suffix of the stratified path 
*)
type stratification_result = { lookup_result : lookup_state; protected : bool ; new_element : Path.elem_t } 

(** The target of a stratified path *)
let target { lookup_result; protected; new_element} =
  let parent =
  if protected then
    (Path.snoc lookup_result.current_path `Protected)
  else
    lookup_result.current_path
  in
  Path.snoc parent new_element

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

let rec norm_recursive {lookup_recursion_term = rec_term;
                        lookup_recursion_state;
                        lookup_recursion_todo} =  
  (* BatLog.logf "Recursively unfolding %s\n" (show_class_term rec_term.rec_rhs) ; *)
  match Path.rear rec_term.rec_lhs with
    Some (xs, (`ClassMember _ | `FieldType _ | `SuperClass _ as k)) ->
    Report.do_ ;                                                  
    (* Unfold the recursive value one level *)
    o <-- output ;
    let lookup_result = forward_state (state_of_lib o) xs in
    let protected = match Path.rear xs with Some(_, `Protected) -> true | _ -> false in
    n <-- norm {lookup_result; protected; new_element=k} rec_term.rec_rhs ;
    set_output (update rec_term.rec_lhs n o) ;

    (* Lookup in the result of the unfolding *)
    begin match get_class_element lookup_recursion_state k n lookup_recursion_todo with
        Success {lookup_success_value} -> return lookup_success_value
      | Error result -> fail_lookup result
      | Recursion r -> norm_recursive r
    end              
  | None -> fail

and norm lhs =
  let open Normalized in
  function
    Empty {class_sort; class_name} -> (if DQ.is_empty class_name then BatLog.logf "Empty class name for %s!\n" (Path.show (target lhs)) else ()) ;
    Report.do_ ;
    return (Class {empty_object_struct with object_sort = class_sort ; source_path = target lhs})

  | Delay rec_rhs ->
    return (Recursive {rec_lhs=target lhs;rec_rhs})

  | Close ->
    Report.do_ ; o <-- output ;
    begin match lookup_path_direct o (target lhs) with
        `Found {found_value} -> return found_value
      | `Recursion _ ->
        BatLog.logf "Internal error. Trying to close a recursive element.\n";
        fail
      | `NothingFound | `PrefixFound _ as result ->
        BatLog.logf "Could not find closed scope\n";
        fail_unresolved {searching=Name.of_ptr lhs.lookup_result.current_path; result}
    end

  | RedeclareExtends ->
    begin match DQ.rear lhs.lookup_result.history with
      (* redeclared is the class containing the virtual extends statement *)
        Some(history, {entry_kind=(`FieldType x | `ClassMember x); entry_structure=redeclared}) ->
        begin match DQ.rear history with
          (* tip of history is enclosing class containing the replaceable *)
            Some(_, {entry_structure=os; entry_kind}) ->
            (* Go back in scope *)
            let state = state_of_history history in

            (* Create a virtual lookup target by removing all elements *)
            let base_only = {os with public = {empty_elements with super = os.public.super};
                                     protected = {empty_elements with super = os.protected.super}} in
            begin
              match get_class_element_os state base_only {ident={txt=x; loc=Location.none};subscripts=[]} [] with
                Success {lookup_success_value} -> return lookup_success_value
                                                    
              | Recursion _ -> Report.do_ ;
                log{where=none;level=Error;what="Trying to extend from recursive element."};
                fail

              | Error result ->
                Report.do_ ;
                log{where=none;level=Error;
                    what=Printf.sprintf "Could not find redeclared base class %s\n" x};
                fail_lookup result
            end
          | _ -> BatLog.logf "Illegal redeclare extends\n"; fail
        end
      | None -> BatLog.logf "Illegal redeclare extends: No enclosing class found."; fail
      | Some (xs,x) -> BatLog.logf "Illegal redeclare extends: Enclosing is: '%s'\n" (show_history_entry_kind x.entry_kind) ; fail
    end

  | RootReference r ->
    Report.do_ ;
    global <-- output ;
    let name = List.map (fun ident -> {Syntax.ident;subscripts=[]}) r in
    let la = lookup global name in
    begin match la with
        Success {lookup_success_state={current_path}} ->
        return (GlobalReference current_path)
      | Recursion {lookup_recursion_state={current_path}; lookup_recursion_todo = []} ->
        return (GlobalReference current_path)
      | Recursion r ->
        norm_recursive r
      | Error err -> fail_lookup err 
    end

  | KnownPtr p -> Report.do_ ;
    strat <-- stratify_ptr p ;
    return (DynamicReference (target strat))

  | Reference n ->
    let components = List.map (fun ident -> {Syntax.ident;subscripts=[]}) n in
    begin match components with
        x::xs ->
        begin match lookup_lexical_in lhs.lookup_result x xs with
            Success {lookup_success_state={current_path}; lookup_success_value} ->
            begin match lhs.new_element with
                `SuperClass _ ->
                (* Decompress superclasses on the fly - this should speed up later passes, otherwise yield a GlobalReference! *)
                return lookup_success_value
              | _ -> 
                return (DynamicReference current_path)
            end
        | Error err ->
          fail_lookup err
        | Recursion r -> norm_recursive r
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
    let o' = update (target lhs) (norm_cv norm) o in
    set_output (o') ;
    norm_prog (i+1) p

open FileSystem

let link_unit linkage {Trans.class_code} = linkage @ class_code

let rec link_package linkage {sub_packages; external_units; package_unit} =
  List.fold_left link_package (List.fold_left link_unit (link_unit linkage package_unit) external_units) sub_packages

let link_root {root_units; root_packages} =
  List.fold_left link_package (List.fold_left link_unit [] root_units) root_packages

type open_term = { open_lhs : Path.t ;
                   open_rhs : rec_term }

let rec collect_recursive_terms p rts = function
    Class os -> let rts' =
                  elements_collect_recursive_terms p rts os.public in
    elements_collect_recursive_terms (DQ.snoc p `Protected) rts' os.protected

  | Constr {arg} -> collect_recursive_terms p rts arg
  | Replaceable v -> collect_recursive_terms p rts v
  | Recursive open_rhs -> {open_lhs = p; open_rhs}::rts
  | v -> rts

and elements_collect_recursive_terms p rts {class_members; fields;} =
  let rts' = StrMap.fold (fun k v rts -> collect_recursive_terms (DQ.snoc p (`ClassMember k)) rts v.class_) class_members rts in
  StrMap.fold (fun k v rts -> collect_recursive_terms (DQ.snoc p (`FieldType k)) rts v.field_class) fields rts'               

let rec close_terms i p =
  Report.do_ ;
  o <-- output;
  if i >= Array.length p then return o
  else
    let {open_lhs;open_rhs} = p.(i) in
    Report.do_ ;
    (* let () = BatLog.logf "Close [%d / %d] %s := %s\n" i (Array.length p) (show_class_path open_lhs) (show_class_term open_rhs.rec_rhs) in *)
    lhs <-- stratify_ptr (open_lhs :> class_ptr) ;
    (* Continue normalization *)
    let r = {lookup_recursion_state = lhs.lookup_result ;
             lookup_recursion_todo = [] ;
             lookup_recursion_term = open_rhs } in    
    closed <-- norm_recursive r ;
    set_output (update open_lhs closed o) ;
    close_terms (i+1) p

let norm_pkg_root root =
  let linkage = link_root root in
  let cc = preprocess linkage in
  Report.do_ ;
  (* normalize signature *)
  o <-- norm_prog 0 cc ;
  (* compress the result *)
  let c = compress_elements o in
  (* close recursive terms *)
  let ct = Array.of_list (elements_collect_recursive_terms DQ.empty [] c) in
  o <-- close_terms 0 ct ;
  return o



