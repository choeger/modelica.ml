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

module CamlFormat = Format
open Batteries
module Format = CamlFormat
                  
open Utils
open Location
open Motypes
open Report
       
exception ExpansionException of string
                                        
type prefix_found_struct = { found : class_path ; not_found : Name.t } [@@deriving show]

let show_prefix_found {found; not_found} = "No element named " ^ (Name.show not_found) ^ " in " ^ (Name.show (Name.of_ptr found))
                      
type found_struct = { found_path : class_path ; found_value : Normalized.class_value ; found_visible : bool } [@@deriving show]

type search_error = [ `NothingFound | `PrefixFound of prefix_found_struct ] [@@deriving show]

type found_recursion = { rec_term : Normalized.rec_term ; search_state : prefix_found_struct } [@@deriving show]
                                                                            
type search_result = [`Found of found_struct | `Recursion of found_recursion | search_error ] [@@deriving show]
                                                   
type unresolved_dependency = { searching : Name.t ; result : search_error }
                               
let fail_unresolved {searching; result} = Report.do_ ; log{level=Error;where=none;what=Printf.sprintf "Dependency %s not evaluated:\n%s\n" (Name.show searching)
                                                                                                      (show_search_error result)} ; fail

exception EmptyName
                                                                                                                                      
let rec get_class_element_in global current_path {Normalized.class_members; super; fields} x xs =
  if StrMap.mem x class_members then begin
      let found = (DQ.snoc current_path (`ClassMember x)) in
      let r = (get_class_element global found (StrMap.find x class_members) xs) in
      match r with
        `NothingFound -> (`PrefixFound {not_found=xs; found})      
      | r -> r
    end
  else if StrMap.mem x fields then begin
      let found = (DQ.snoc current_path (`Field x)) in
      let r = (get_class_element global found (StrMap.find x fields) xs) in
      match r with
        `NothingFound -> (`PrefixFound {not_found=xs; found})      
      | r -> r
    end
  else
    pickfirst_class global 0 current_path (DQ.snoc xs x) (IntMap.bindings super)

and pickfirst_class global n current_path name = function
    [] -> `NothingFound
  | (k,v)::vs ->
     let next_path = DQ.snoc current_path (`SuperClass n) in
     let f = get_class_element global next_path v name in
     begin match f with
             `NothingFound -> pickfirst_class global (n+1) current_path name vs
           | r -> r
     end
                    
and get_class_element global found_path e p =
  let open Normalized in 
  match DQ.front p with
    None -> (`Found {found_path ; found_value = e; found_visible=true})
  | Some (x, xs) -> begin
      match e with
      | Class {protected;public} ->
         let f = get_class_element_in global found_path public x xs in
         begin
           match f with
             `NothingFound -> get_class_element_in global found_path protected x xs
           | _ as r -> r
         end

      (* we might encounter recursive elements *)
      | Recursive rec_term -> `Recursion {rec_term; search_state={found = found_path; not_found = p}}
           
      (* we might encounter a global reference due to the scc resolution *)
      | GlobalReference g ->
         BatIO.flush (!BatLog.output);
         BatLog.logf "Following %s in search for %s\n" (Name.show g) (Name.show p);
         begin match DQ.front g with
                 Some(x,xs) ->
                 begin match get_class_element_in global DQ.empty global x xs with
                       | `Found {found_value} -> get_class_element global found_path found_value p
                       | `NothingFound | `PrefixFound _ as result ->  BatLog.logf "Could not follow (probably recursive) %s\n" (Name.show g); result
                 end
               | None -> raise EmptyName
         end
                               
      | Constr {arg} -> get_class_element global found_path arg p
      | _ -> `NothingFound
    end    
                                          
let lookup o p =
  let open Normalized in
  match DQ.front p with
    None -> (`Found {found_value = Class {empty_object_struct with public = o}; found_path = DQ.empty; found_visible=true}) ;
  | Some(x,xs) -> get_class_element_in o DQ.empty o x xs


open Normalized

exception IllegalPathElement 
                                    
exception CannotUpdate of string * string * string

let rec update (lhs:class_path) rhs ({class_members;fields;super} as elements) = match DQ.front lhs with
    None -> elements
  | Some (`SuperClass i, r) -> {elements with super = update_super r rhs i super} 
  | Some (`Field x, r) -> {elements with fields = update_map r rhs x fields}
  | Some (`ClassMember x, r) -> {elements with class_members = update_map r rhs x class_members}
  | Some (`Protected,_) -> raise IllegalPathElement

and update_map lhs rhs x m =  
  StrMap.modify_def empty_class x (update_class_value lhs rhs) m
                                     
and update_super lhs rhs i super =  
  IntMap.modify_def empty_class i (update_class_value lhs rhs) super

and update_class_value lhs rhs = function
  | Constr {constr; arg} -> Constr {constr ; arg = (update_class_value lhs rhs arg)}
  | Class ({public; protected} as os) -> begin match DQ.front lhs with
                                                 None -> rhs
                                               | Some(`Protected, q) -> Class {os with protected = update q rhs protected}
                                               | Some _ -> Class {os with public = update lhs rhs public}
                                         end
  | Replaceable cv -> Replaceable (update_class_value lhs rhs cv)
  | (Recursive _ | Int | Real | String | Bool | Unit | ProtoExternalObject | Enumeration _ | GlobalReference _) as v ->
     begin match DQ.front lhs with
             None -> rhs
           | Some (x,xs) -> raise (CannotUpdate(show_class_path_elem x, show_class_path xs, show_class_value v))
     end
                                       
exception NonLeafRecursion

exception Stratification of class_path * string
       
let rec stratify_non_existing done_ todo = match DQ.front todo with
    None -> done_
  | Some(`Any x, _) -> raise (Stratification (done_, x))
  | Some((`Protected | `ClassMember _ | `Field _ | `SuperClass _) as x, xs) -> stratify_non_existing (DQ.snoc done_ x) xs
    
let rec stratify global c done_ (todo:class_ptr) =
  match DQ.front todo with
    None -> done_
  | Some(`Any x,xs) -> begin match get_class_element global DQ.empty c (DQ.singleton x) with
                               `Found {found_value;found_path} -> begin match DQ.front found_path with
                                                                          None -> raise (Failure "internal error, succeeded lookup returned empty path") 
                                                                        | Some (y, ys) -> stratify global found_value (DQ.snoc done_ y) xs
                                                                  end
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
       
and stratify_elements global ({class_members; super; fields} as es) done_ (todo:class_ptr) =
  match DQ.front todo with
    | None -> done_
    | Some(`Field x, xs) when StrMap.mem x fields -> stratify global (StrMap.find x fields) (DQ.snoc done_ (`Field x)) xs 
    | Some(`ClassMember x, xs) when StrMap.mem x class_members -> stratify global (StrMap.find x class_members) (DQ.snoc done_ (`ClassMember x)) xs 
    | Some(`SuperClass i, xs) when IntMap.mem i super -> stratify global (IntMap.find i super) (DQ.snoc done_ (`SuperClass i)) xs

    | Some (`Protected, xs) -> raise IllegalPathElement

    | Some(`Any x, xs) -> begin match get_class_element_in global DQ.empty es x DQ.empty with
                                  `Found {found_value;found_path} -> begin match DQ.front found_path with
                                                                             None -> raise (Failure "internal error, succeeded lookup returned empty path") 
                                                                           | Some (y, ys) -> stratify global found_value (DQ.snoc done_ y) xs
                                                                    end
                                | _ -> raise (Stratification (done_, x))
                          end
    | Some _ -> stratify_non_existing done_ todo

let stratify_ptr ptr =
  Report.do_ ;
  o <-- output ;
  try return (stratify_elements o o DQ.empty ptr) with
  | Stratification (found, not_found) ->
     Report.do_ ;
     log{level=Error;where=none;what=Printf.sprintf "Stratification error: No element %s in %s" not_found (show_class_ptr found)};fail

            
let rec find_lexical global previous path ctxt x current =
  match DQ.front ctxt with
    None -> begin
      match get_class_element global path current (DQ.singleton x) with
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
                                                  BatLog.logf "Recursively unfolding %s\n" (show_class_term rec_term.rec_rhs) ;
                                                  Report.do_ ;                                                  
                                                  n <-- norm lhs rec_term.rec_rhs ;
                                                  o <-- output ;
                                                  match get_class_element o search_state.found n search_state.not_found with
                                                    `Found {found_value = Replaceable v} -> return (GlobalReference name)
                                                  | `Found {found_value} -> return found_value
                                                  | `NothingFound | `PrefixFound _ as result -> fail_unresolved {searching=name; result}
                                                  | `Recursion r -> norm_recursive r
                                                                                                                
and norm lhs =
                                                              
  let open Normalized in
  function
    Empty {class_sort; class_name} -> return (Class {empty_object_struct with object_sort = class_sort ; source_name = class_name})
  | Delay rec_rhs -> return (Recursive {rec_lhs=lhs;rec_rhs})

  | Close ->
     let name = Name.of_ptr lhs in
     Report.do_ ; o <-- output ; begin match lookup o name with
                                         `Found {found_value} -> return found_value
                                       | `NothingFound | `PrefixFound _ as result ->  BatLog.logf "Could not find closed scope\n"; fail_unresolved {searching=name; result}
                                 end

  | RedeclareExtends -> begin match DQ.rear lhs with
                                Some(parent, `SuperClass _) -> begin match DQ.rear parent with
                                                                       Some(enclosing, `ClassMember id) -> Report.do_ ; o <-- output ;
                                                                                                           let name = (Name.of_ptr parent) in
                                                                                                           begin match lookup o name with
                                                                                                                 | `Found {found_value} -> return found_value
                                                                                                                 | `NothingFound | `PrefixFound _ as result ->  BatLog.logf "Could not find redeclared base class %s\n" id; fail_unresolved {searching=name; result}     
                                                                                                           end
                                                                     | _ ->  BatLog.logf "Illegal redeclare extends\n"; fail
                                                               end
                              | _ -> BatLog.logf "Illegal redeclare extends\n"; fail
                        end

  | RootReference n -> return (GlobalReference (Name.of_list (lunloc n)))

  | Reference n ->
     let ctxt = Name.scope_of_ptr lhs in
     let name = Name.of_list (lunloc n) in
     let previous = `NothingFound in
     begin match DQ.front name with
             Some(x, xs) ->
             Report.do_ ; o <-- output ;
             begin match find_lexical o previous DQ.empty ctxt x (Class {empty_object_struct with public = o}) with
                   | `Recursion r -> norm_recursive {r with search_state = {r.search_state with not_found = xs}}
                   | `Found {found_value = Replaceable v ; found_path} -> return (GlobalReference (DQ.append (Name.of_ptr found_path) xs))
                   | `Found {found_value;found_path} -> begin match get_class_element o found_path found_value xs with
                                                              | `Recursion r -> norm_recursive r
                                                              | `Found {found_value = Replaceable v} -> return (GlobalReference (DQ.append (Name.of_ptr found_path) xs))
                                                              | `Found {found_value} -> return found_value
                                                              | `NothingFound | `PrefixFound _ as result -> BatLog.logf "Could not find suffix\n"; fail_unresolved {searching=name; result}
                                                        end
                   | `NothingFound | `PrefixFound _ as result ->  BatLog.logf "Could not find prefix\n"; fail_unresolved {searching=name; result}
             end
           | None -> Report.do_; log{level=Error; where=none; what=Printf.sprintf "Empty name when evaluating %s. Most likely an internal bug." (show_class_ptr lhs)} ; fail
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
                                              
let rec norm_prog i p =
    Report.do_ ;
    o <-- output;
    if i >= Array.length p then return o
    else
      let {lhs;rhs} = p.(i) in
      Report.do_ ;
      lhs <-- stratify_ptr lhs ;
      let () = BatLog.logf "[%d / %d] %s := %s\n" i (Array.length p) (show_class_ptr lhs) (show_class_term rhs) in      
      norm <-- norm lhs rhs;
      set_output (update lhs norm o) ;
      norm_prog (i+1) p

open ClassDeps

                                                   
open FileSystem
       

let link_unit linkage {ClassTrans.class_code} = linkage @ class_code

let rec link_package linkage {sub_packages; external_units; package_unit} =
  List.fold_left link_package (List.fold_left link_unit (link_unit linkage package_unit) external_units) sub_packages

let link_root {root_units; root_packages} =
  List.fold_left link_package (List.fold_left link_unit [] root_units) root_packages
                 
let norm_pkg_root root =
  let linkage = link_root root in
  let cc = preprocess linkage in
  norm_prog 0 cc
  
  
