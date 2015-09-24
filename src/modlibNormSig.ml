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

let rec stratify_non_existing done_ todo = match DQ.front todo with
    None -> done_
  | Some(`Any x, _) -> raise (Stratification (done_, x))
  | Some((`Protected | `ClassMember _ | `FieldType _ | `SuperClass _ ) as x, xs) -> stratify_non_existing (DQ.snoc done_ x) xs

let rec stratify global c (done_:class_path) (todo:class_ptr) =
  match DQ.front todo with
    None -> done_
  | Some(`Any x,xs) -> begin match get_class_element global DQ.empty c (DQ.singleton x) with
        `Found {found_value;found_path} -> stratify_continue global found_value done_ xs found_path
      | _ -> raise (Stratification (done_, x))
    end

  | Some(`Protected, xs) -> 
    begin match c with
        Class {protected} -> stratify_elements global protected (DQ.snoc done_ `Protected) xs
      | _ -> stratify_non_existing done_ todo
    end
  | Some(x,xs) -> begin match c with
        Class {public} -> stratify_elements global public done_ todo
      | _ -> stratify_non_existing done_ todo
    end

and stratify_continue global found_value done_ todo found_path = match DQ.rear found_path with
    None -> raise (Failure "internal error, succeeded lookup returned empty path") 
  | Some (ys,y) -> stratify global found_value (DQ.snoc (stratify_append done_ ys) y) todo
  
and stratify_append done_ found_prefix = match DQ.rear found_prefix with 
  | Some(_, (`Protected as x)) -> DQ.snoc done_ x
  | _ -> done_

and stratify_elements global ({class_members; super; fields} as es) (done_:class_path) (todo:class_ptr) =
  match DQ.front todo with
  | None -> done_
  | Some(`FieldType x, xs) when StrMap.mem x fields -> stratify global (StrMap.find x fields).field_class (DQ.snoc done_ (`FieldType x)) xs 
  | Some(`ClassMember x, xs) when StrMap.mem x class_members -> stratify global (StrMap.find x class_members) (DQ.snoc done_ (`ClassMember x)) xs 
  | Some(`SuperClass i, xs) when IntMap.mem i super -> stratify global (IntMap.find i super) (DQ.snoc done_ (`SuperClass i)) xs

  | Some (`Protected, xs) -> raise (IllegalPath "protected")

  | Some(`Any x, xs) -> begin match get_class_element_in global DQ.empty es x DQ.empty with
        `Found {found_value;found_path} -> stratify_continue global found_value done_ xs found_path
      | _ -> raise (Stratification (done_, x))
    end
  | Some _ -> stratify_non_existing done_ todo

let stratify_ptr ptr =
  Report.do_ ;
  o <-- output ;
  try return (stratify_elements o o DQ.empty ptr) with
  | Stratification (found, not_found) ->
    Report.do_ ;
    log{level=Error;where=none;what=Printf.sprintf "Stratification error: No element %s in %s" not_found (show_class_path found)}; fail


let rec find_lexical global previous path ctxt x current =
  match DQ.front ctxt with
    None -> begin
      let r = get_class_element global path current (DQ.singleton x) in
      match r with
        (`Found _ | `Recursion _) as f -> f                                                                                                 
      | _ -> previous
    end
  | Some(y, p) ->
    let previous' = 
      match get_class_element global path current (DQ.singleton x) with
        (`Found _ | `Recursion _) as f -> f                                                                                                 
      | _ -> previous
    in
    match get_class_element global path current (DQ.singleton y) with
      `Found {found_value;found_path} ->       
      find_lexical global previous' found_path p x found_value
    | `Recursion _ -> raise NonLeafRecursion
    | _ -> previous'

let rec norm_recursive {rec_term; search_state} = let name = (DQ.append (Name.of_ptr search_state.found) search_state.not_found) in
  let lhs = rec_term.rec_lhs in
  (* BatLog.logf "Recursively unfolding %s\n" (show_class_term rec_term.rec_rhs) ; *)
  Report.do_ ;                                                  
  n <-- norm lhs rec_term.rec_rhs ;
  o <-- output ;
  value <-- begin
    match get_class_element o search_state.found n search_state.not_found with
      `Found {found_value = Replaceable _; found_path} ->
      return (GlobalReference found_path)
    | `Found {found_value} -> return found_value
    | `NothingFound | `PrefixFound _ as result -> fail_unresolved {searching=name; result}
    | `Recursion r -> norm_recursive r
  end ;
  set_output (update lhs value o) ;
  return value

and norm lhs =

  let open Normalized in
  function
    Empty {class_sort; class_name} -> (if DQ.is_empty class_name then BatLog.logf "Empty class name for %s!\n" (show_class_path lhs) else ()) ;
    Report.do_ ;
    return (Class {empty_object_struct with object_sort = class_sort ; source_path = lhs})
  | Delay rec_rhs -> return (Recursive {rec_lhs=lhs;rec_rhs})

  | Close ->
    Report.do_ ; o <-- output ; begin match lookup_path o lhs with
        `Found {found_value} -> return found_value
      | `Recursion _ ->
        BatLog.logf "Internal error. Trying to close a recursive element.\n";
        fail
      | `NothingFound | `PrefixFound _ as result ->
        BatLog.logf "Could not find closed scope\n";
        fail_unresolved {searching=Name.of_ptr lhs; result}
    end

  | RedeclareExtends -> begin match DQ.rear lhs with
        Some(parent, `SuperClass _) -> begin match DQ.rear parent with
            Some(enclosing, (`ClassMember id | `FieldType id)) -> Report.do_ ; o <-- output ;
            begin match lookup_path o enclosing with
              | `Found {found_value=Class os} ->
                begin
                  (*BatLog.logf "Enclosing class source name: %s\n" (Name.show os.source_name) ;*)
                  let base_only = Class {os with public = {empty_elements with super = os.public.super};
                                                 protected = {empty_elements with super = os.protected.super}} in

                  match get_class_element o enclosing base_only (DQ.singleton id) with

                    `Found {found_value;found_path} -> (*BatLog.logf "Found redeclare-base (%s): \n%s\n" id (show_class_value found_value);*) return found_value

                  | `Recursion _ -> Report.do_ ;
                    log{where=none;level=Error;what="Trying to extend from recursive element."};
                    fail

                  | `NothingFound | `PrefixFound _ as result ->
                    Report.do_ ;
                    log{where=none;level=Error;
                        what=Printf.sprintf "Could not find redeclared base class %s\n" id};
                    fail_unresolved {searching=Name.of_ptr enclosing; result}
                end
              | `NothingFound | `PrefixFound _ as result ->
                BatLog.logf "Could not find parent of redeclared base class %s\n" id;
                fail_unresolved {searching=Name.of_ptr enclosing; result}     
              | _ -> BatLog.logf "Internal error. Parent of redeclare-extends is not a class.\n"; fail
            end
          | _ ->  BatLog.logf "Illegal redeclare extends\n"; fail
        end
      | _ -> BatLog.logf "Illegal redeclare extends\n"; fail
    end

  | RootReference (x::xs) ->
    Report.do_ ;
    global <-- output ;
    let name = Name.of_list (lunloc xs) in
    let la = get_class_element_in global DQ.empty global x.txt name in
    begin match la with
        `Found {found_path} -> return (GlobalReference found_path)
      | `Recursion {search_state={found;not_found}} when not_found = DQ.empty ->
        return (GlobalReference found)
      | `Recursion {rec_term} -> return (Recursive rec_term)
      | `NothingFound | `PrefixFound _ as result ->
        fail_unresolved {searching = DQ.cons x.txt name; result}
    end

  | KnownPtr p -> Report.do_ ;
    path <-- stratify_ptr p ;
    return (GlobalReference path)

  | Reference n ->
    let ctxt = Name.scope_of_ptr lhs in
    let name = Name.of_list (lunloc n) in
    let previous = `NothingFound in
    begin match DQ.front name with
      (* first, do a lookup in scope of the first identifier *)
        Some(x, xs) ->
        Report.do_ ; o <-- output ;
        let lookup = find_lexical o previous DQ.empty ctxt x
            (Class {empty_object_struct with public = o})
        in   
        begin match lookup with
          | `Recursion r ->
            norm_recursive {r with search_state =
                                     {r.search_state with not_found = xs}}
          | `Found fs ->
            (* Now lookup the rest of the name *)
            let lookup_rhs = get_class_element o fs.found_path
                fs.found_value xs 
            in
            begin match lookup_rhs with
                `Found {found_replaceable=true; found_path} ->
                return (DynamicReference found_path)
              | `Found {found_path} when fs.found_replaceable ->
                return (DynamicReference found_path)
              | `Found {found_value=Class os} ->
                (* Compress references to classes on-the-fly *)
                return (GlobalReference os.source_path)                  
              | `Found {found_value} ->
                return found_value
              | `NothingFound | `PrefixFound _ as result ->
                fail_unresolved {searching=name; result}
              | `Recursion r -> norm_recursive r
            end
          | `NothingFound | `PrefixFound _ as result ->
            BatLog.logf "Could not find prefix %s in %s\n" x (Name.show ctxt) ;
            fail_unresolved {searching=name; result}
        end
      | None -> Report.do_;
        log{level=Error; where=none;
            what=Printf.sprintf
                "Empty name when evaluating %s. Most likely an internal bug."
                (show_class_path lhs)} ;
        fail
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

and el_check {class_members} = StrMap.iter (fun k v -> check v) class_members

let rec norm_prog i p =
  Report.do_ ;
  o <-- output;
  if i >= Array.length p then return o
  else
    let {lhs;rhs} = p.(i) in
    Report.do_ ;
    let () = BatLog.logf "[%d / %d] %s\n" i (Array.length p) (show_class_stmt p.(i)) in
    lhs <-- stratify_ptr lhs ;
    norm <-- norm lhs rhs;
    let o' = update lhs (norm_cv norm) o in
    set_output (o') ;
    norm_prog (i+1) p

open FileSystem

let link_unit linkage {Trans.class_code} = linkage @ class_code

let rec link_package linkage {sub_packages; external_units; package_unit} =
  List.fold_left link_package (List.fold_left link_unit (link_unit linkage package_unit) external_units) sub_packages

let link_root {root_units; root_packages} =
  List.fold_left link_package (List.fold_left link_unit [] root_units) root_packages

type open_term = { open_lhs : class_path ;
                   open_rhs : rec_term }


let rec resolve_recursive {rec_term; search_state} = let name = (DQ.append (Name.of_ptr search_state.found) search_state.not_found) in
  let lhs = rec_term.rec_lhs in
  (*BatLog.logf "Recursively unfolding %s\n" (show_class_term rec_term.rec_rhs) ;*)
  Report.do_ ;                                                  
  n <-- norm lhs rec_term.rec_rhs ;
  o <-- output ;                                                       
  match get_class_element o search_state.found n search_state.not_found with
  | `Found {found_path} -> return found_path
  | `NothingFound | `PrefixFound _ as result -> fail_unresolved {searching=name; result}
  | `Recursion r -> resolve_recursive r


and resolve lhs n =
  let ctxt = Name.scope_of_ptr lhs in
  let name = Name.of_list (lunloc n) in
  let previous = `NothingFound in
  begin match DQ.front name with
      Some(x, xs) ->
      Report.do_ ; o <-- output ;
      begin match find_lexical o previous DQ.empty ctxt x (Class {empty_object_struct with public = o}) with
        | `Recursion r -> resolve_recursive {r with search_state = {r.search_state with not_found = xs}}
        | `Found {found_value;found_path} -> begin match get_class_element o found_path found_value xs with
            | `Recursion r -> resolve_recursive r
            | `Found {found_path} -> return found_path
            | `NothingFound | `PrefixFound _ as result -> BatLog.logf "Could not find suffix\n"; fail_unresolved {searching=name; result}
          end
        | `NothingFound | `PrefixFound _ as result ->  BatLog.logf "Could not find prefix\n"; fail_unresolved {searching=name; result}
      end
    | None -> Report.do_; log{level=Error; where=none; what=Printf.sprintf "Empty name when evaluating %s. Most likely an internal bug." (show_class_ptr lhs)} ; fail
  end

let rec close_term lhs = function
  | RedeclareExtends | Empty _ | Delay _ | Close -> Report.do_ ; Report.log {what=Printf.sprintf "Error closing %s. Cannot close artificial class-statements." (show_class_path lhs);level=Error;where=none}; fail


  | RootReference (x::xs) -> do_ ;
    o <-- output ;
    let name = (Name.of_list (lunloc xs)) in
    let la = get_class_element_in o DQ.empty o x.txt name in
    begin match la with
        `Found {found_path} -> return (GlobalReference found_path)
      | `Recursive r -> do_ ;
        p <-- resolve_recursive r ;
        return (GlobalReference p)
      | `NothingFound | `PrefixFound _ as result ->
        fail_unresolved {searching=DQ.cons x.txt name; result}
    end  

  | KnownPtr p ->
    Report.do_ ;
    path <-- stratify_ptr p ;		  
    return (GlobalReference path)

  | Reference n -> Report.do_ ;
    p <--resolve (lhs :> class_ptr) n ;
    return (GlobalReference p)

  | Constr {constr=CRepl; arg} -> Report.do_ ;
    argv <-- close_term lhs arg ;
    return (Replaceable argv) 

  | Constr {constr; arg} -> Report.do_ ;
    argv <-- close_term lhs arg ;
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

let rec collect_recursive_terms p rts = function
    Class os -> let rts' =
                  elements_collect_recursive_terms p rts os.public in
    elements_collect_recursive_terms (DQ.snoc p `Protected) rts' os.protected

  | Constr {arg} -> collect_recursive_terms p rts arg
  | Replaceable v -> collect_recursive_terms p rts v
  | Recursive open_rhs -> {open_lhs = p; open_rhs}::rts
  | v -> rts

and elements_collect_recursive_terms p rts {class_members; fields;} =
  let rts' = StrMap.fold (fun k v rts -> collect_recursive_terms (DQ.snoc p (`ClassMember k)) rts v) class_members rts in
  StrMap.fold (fun k v rts -> collect_recursive_terms (DQ.snoc p (`FieldType k)) rts v.field_class) fields rts'               

let rec close_terms i p =
  Report.do_ ;
  o <-- output;
  if i >= Array.length p then return o
  else
    let {open_lhs;open_rhs} = p.(i) in
    Report.do_ ;
    (*let () = BatLog.logf "Close [%d / %d] %s := %s\n" i (Array.length p) (show_class_path open_lhs) (show_class_term open_rhs.rec_rhs) in *)
    closed <-- close_term open_rhs.rec_lhs open_rhs.rec_rhs;
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
  let () = BatLog.logf "Done.\n%!" in
  return o



