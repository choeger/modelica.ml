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

(* compression of Modelica library signatures *)

open Batteries
open Utils
open Location
open Report

module Inter = ModlibInter
module Normalized = ModlibNormalized
module Lookup = ModlibLookup

open Inter
open Normalized
open Lookup

type decompression = {
  parent_class : class_path ;
  superclass_nr : int;
  superclass_name : class_path ;
}

let rec compress = function
(*    Class os ->
    Class {os with public = compress_elements os.public; protected = compress_elements os.protected }
  | Constr {constr; arg} -> Constr {constr; arg = compress arg}
      | Replaceable v -> Replaceable (compress v) *)
  | v -> v
(*
and compress_modified_class cm = {cm with class_ = compress cm.class_}

and compress_super_class sc = match sc.super_shape with 
*)
and compress_elements es = es (*{fields = StrMap.map pack_field es.fields;
                            super = IntMap.map compress_super_class es.super;
                            class_members = StrMap.map compress_modified_class es.class_members }

and pack_field f = {f with field_class = pack_class f.field_class}

and pack_class = function
    Class os -> GlobalReference os.source_path
  | Constr {constr; arg} -> Constr {constr; arg = pack_class arg}
  | Replaceable v -> Replaceable (pack_class v)
  | v -> v

let rec decompressions p dcs = function
    Class os -> let dcs' = elements_decompressions p dcs os.public in
    elements_decompressions (DQ.snoc p `Protected) dcs' os.protected
  | _ -> dcs

and superclass_to_decompress parent_class superclass_nr dcs = function
    GlobalReference superclass_name ->
    {parent_class; superclass_nr ; superclass_name}::dcs
  | Constr {arg} -> superclass_to_decompress parent_class superclass_nr dcs arg
  | _ -> dcs

and elements_decompressions p dcs es =
  let dcs' = IntMap.fold (fun k v dcs -> superclass_to_decompress p k dcs v.class_) es.super dcs in
  StrMap.fold (fun k v dcs -> decompressions (DQ.snoc p (`ClassMember k)) dcs v.class_) es.class_members dcs'

let rec do_decompression i dcs =
  if i >= Array.length dcs then (Report.do_ ; log{where=none;level=Info;what="Finished Decompression"} ; output) else
    let n = dcs.(i).superclass_name in
    match DQ.front n with
      None -> Report.do_ ; log {where=none; level=Error; what="Inconsistent normal form: Empty superclass name."} ; fail
    | Some (x,xs) ->
      Report.do_ ;
      o <-- output ;
      match follow_path_es o DQ.empty o xs x with
        `Recursion _ -> Report.do_ ; log {where=none; level=Error; what="Inconsistent normal form: Recursive Entry found."} ; fail

      | `Found {found_value; found_path} ->
        Report.do_ ;
        set_output (update (DQ.snoc dcs.(i).parent_class (`SuperClass dcs.(i).superclass_nr)) found_value o) ;
        do_decompression (i+1) dcs 

      | `PrefixFound _ | `NothingFound as result ->
        fail_unresolved {searching=Name.of_ptr n; result}


module GInt = struct include Int let hash i = i end
module DepGraph = Graph.Persistent.Digraph.Concrete(GInt)
module Scc = Graph.Components.Make(DepGraph)

(* record all decompressions required for a class-name *)                                  
let decompress_map dcm i {parent_class} =
  if PathMap.mem parent_class dcm then    
    PathMap.add parent_class (i::(PathMap.find parent_class dcm)) dcm
  else
    PathMap.add parent_class [i] dcm

let decompress_dep dcm g i {superclass_name} =
  if PathMap.mem superclass_name dcm then
    List.fold_left (fun g j -> DepGraph.add_edge g i j) g (PathMap.find superclass_name dcm)
  else
    DepGraph.add_vertex g i
*)
let decompress es =
  (*let dcs = Array.of_list (elements_decompressions DQ.empty [] es) in
  let dcm = Array.fold_lefti decompress_map PathMap.empty dcs in
  let dcg = Array.fold_lefti (decompress_dep dcm) DepGraph.empty dcs in
  let sccs = Scc.scc_list dcg in

  let rec reorder_sccs = function
    | [] -> return []
    | []::sccs -> reorder_sccs sccs
    | [i]::sccs -> Report.do_ ;
      sccs' <-- (reorder_sccs sccs) ;
      return (dcs.(i)::sccs')

    | (i::is)::sccs -> let what = Printf.sprintf "Recursive inheritance involving %s" (Path.show dcs.(i).superclass_name) in
      Report.do_ ;
      log {level=Error;what;where=none}; fail
  in  
  *)
  Report.do_ ;
  return es
  (*set_output {o with class_members = StrMap.union o.class_members es.class_members} ;     
  dcs <-- reorder_sccs sccs;
    do_decompression 0 (Array.of_list dcs) *)
  

let load_from_json js =
  let cv = elements_struct_of_yojson js in

  match cv with
    `Error err -> Report.do_; log{where=none; level=Error; what=err} ; fail
  | `Ok es ->
    decompress es
