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

exception ExpansionException of string
exception NonLeafRecursion
exception Stratification of class_path * string

(** 
   A stratification result holds the last valid context of the existing prefix and the non existing suffix of the stratified path 
*)
type stratification_result = { lookup_result : lookup_state; non_existing : Path.t }

(** The target of a stratified path *)
let target { lookup_result; non_existing} = Path.append lookup_result.current_path non_existing

let stratify_non_existing state todo =
  let rec strat_ne sr todo = match DQ.front todo with
      None -> sr
    (** Cannot distinguish an ambigous reference that does not exist yet *)
    | Some(`Any x, _) -> raise (Stratification (Path.append sr.lookup_result.current_path sr.non_existing, x))
    | Some((`Protected | `ClassMember _ | `FieldType _ | `SuperClass _ ) as x, xs) ->
      strat_ne {sr with non_existing = (Path.snoc sr.non_existing x)} xs
  in
  strat_ne {lookup_result=state; non_existing=Path.empty} todo
    
let rec stratify state c (todo:class_ptr) =
  match DQ.front todo with
    None -> {lookup_result = state; non_existing=Path.empty}
  | Some(`Any x,xs) ->
    begin match get_class_element state c [{ident={txt=x;loc=Location.none};subscripts=[]}] with
        Success {lookup_success_state; lookup_success_value} ->
        stratify_continue lookup_success_state lookup_success_value xs
      | _ -> raise (Stratification (state.current_path, x))
    end

  | Some(`Protected, xs) -> 
    begin match c with
        Class ({protected} as os) ->
        let history = append_to_history state os in
        let current_path = DQ.snoc state.current_path `Protected in
        stratify_elements {state with history; current_path} protected xs
      | _ -> raise (ExpansionException "expected a class")
    end
  | Some(x,xs) ->
    begin match c with
        Class ({public} as os) ->
        let history = append_to_history state os in
        stratify_elements {state with history} public todo
      | _ -> raise (ExpansionException "expected a class")
    end

and stratify_continue state found_value todo =
  stratify state found_value todo
  
and stratify_elements state ({class_members; super; fields} as es) (todo:class_ptr) =
  match DQ.front todo with
  | None -> {lookup_result = state; non_existing=Path.empty}
  | Some(`FieldType x, xs) when StrMap.mem x fields ->
    let current_path = DQ.snoc state.current_path (`FieldType x) in    
    stratify {state with current_path} (StrMap.find x fields).field_class xs
      
  | Some(`ClassMember x, xs) when StrMap.mem x class_members ->
    let current_path = DQ.snoc state.current_path (`ClassMember x) in    
    stratify {state with current_path} (StrMap.find x class_members).class_ xs
      
  | Some(`SuperClass i, xs) when IntMap.mem i super ->
    let current_path = DQ.snoc state.current_path (`SuperClass i) in    
    stratify {state with current_path} (IntMap.find i super).class_  xs

  | Some (`Protected, xs) -> raise (IllegalPath "protected")

  | Some (_, _) -> stratify_non_existing state todo

  | Some(`Any x, xs) ->
    begin match get_class_element_in state es {subscripts=[]; ident={txt=x;loc=Location.none}} [] with
        Success {lookup_success_state; lookup_success_value} ->
        stratify_continue lookup_success_state lookup_success_value xs
      | _ -> raise (Stratification (state.current_path, x))
    end

let stratify_ptr ptr =
  Report.do_ ;
  o <-- output ;
  try return (stratify_elements (state_of_lib o) o ptr) with
  | Stratification (found, not_found) ->
    Report.do_ ;
    log{level=Error;where=none;what=Printf.sprintf "Stratification error: No element %s in %s" not_found (show_class_path found)}; fail

let rec norm_recursive {lookup_recursion_term = rec_term;
                        lookup_recursion_state;
                        lookup_recursion_todo} =  
  (* BatLog.logf "Recursively unfolding %s\n" (show_class_term rec_term.rec_rhs) ; *)
  match DQ.rear rec_term.rec_lhs with
    Some (xs,x) ->
    Report.do_ ;                                                  
    (* Unfold the recursive value one level *)
    parent <-- stratify_ptr (xs :> class_ptr) ;
    o <-- output ;
    n <-- norm parent rec_term.rec_rhs ;
    set_output (update rec_term.rec_lhs n o) ;

    (* Lookup in the result of the unfolding *)
    begin match get_class_element lookup_recursion_state n lookup_recursion_todo with
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
    let () = assert (lhs.non_existing = Path.empty) in
    begin match lookup_path_direct o lhs.lookup_result.current_path with
        `Found {found_value} -> return found_value
      | `Recursion _ ->
        BatLog.logf "Internal error. Trying to close a recursive element.\n";
        fail
      | `NothingFound | `PrefixFound _ as result ->
        BatLog.logf "Could not find closed scope\n";
        fail_unresolved {searching=Name.of_ptr lhs.lookup_result.current_path; result}
    end

  | RedeclareExtends ->
    let () = assert (lhs.non_existing = Path.empty) in
    begin match DQ.rear lhs.lookup_result.history with
        Some (redeclared, {entry_structure; entry_kind=`SuperClass _}) ->
        begin match DQ.rear redeclared with
          (* redeclared is the class containing the virtual extends statement *)
            Some(enclosing, {entry_kind=`ClassMember x}) -> begin match DQ.rear enclosing with
              (* enclosing is the class containing the replaceable *)
                Some(history, {entry_structure=os; entry_kind}) ->
                (* Go back in scope *)
                let state =
                  {history;
                   trace = DQ.empty ; current_ref = DQ.empty; current_attr = no_attributes;
                   current_path = path_of_history enclosing}  in
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
          | _ -> BatLog.logf "Illegal redeclare extends\n"; fail
        end
      | _ -> BatLog.logf "Illegal redeclare extends\n"; fail
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
    return (GlobalReference (target strat))

  | Reference n ->
    let components = List.map (fun ident -> {Syntax.ident;subscripts=[]}) n in
    begin match components with
      x::xs ->
      begin match lookup_in lhs.lookup_result x xs with
          Success {lookup_success_state={trace}; lookup_success_value} ->
          begin match DQ.front trace with
            | Some (x,_) -> return (GlobalReference x)
            | None -> return lookup_success_value
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
    let {lhs;rhs} = p.(i) in
    Report.do_ ;
    lhs <-- stratify_ptr lhs ;
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
    (*let () = BatLog.logf "Close [%d / %d] %s := %s\n" i (Array.length p) (show_class_path open_lhs) (show_class_term open_rhs.rec_rhs) in *)
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



