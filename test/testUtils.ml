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
(** A bunch of combinators/constructors for (source based) test cases, needs cleanup *)

open OUnit2
open Batteries
open Sexplib
       
module Diff :
sig
  type t
  val print : ?oc:out_channel -> t -> unit
  val to_buffer : t -> Buffer.t
  val to_string : t -> string
  val of_sexps : original:Sexp.t -> updated:Sexp.t -> t option
end
=
struct
  type t =
      | Different of ([`Original of Sexp.t] * [`Updated of Sexp.t])
      | List of t list
      | Record of record_field list

  and record_field =
      | New_in_updated of Sexp.t
      | Not_in_updated of Sexp.t
      | Bad_match of string * t

  let rec rev_map_append f l1 l2 =
    match l1 with
    | [] -> l2
    | h :: t -> rev_map_append f t (f h :: l2)

  let make_tail make tail acc =
    Some (Record (List.rev (rev_map_append make tail acc)))

  let recf (k, v) = Sexp.List [Sexp.Atom k; v]

  let maybe_record sexps =
    let is_list_of_atom_pairs = function
      | Sexp.List [Sexp.Atom _; _] -> true
      | _ -> false
    in
    sexps <> [] &&
      (List.for_all is_list_of_atom_pairs sexps)

  let sort_record_fields sexp_list =
    let to_pair = function
      | Sexp.List [Sexp.Atom k; v] -> k, v
      | _ -> assert false  (* impossible *)
    in
    let pairs = List.map to_pair sexp_list in
    List.sort (fun (k1, _) (k2, _) -> compare k1 k2) pairs

  let rec of_record_fields acc pairs_orig pairs_upd =
    match pairs_orig, pairs_upd with
    | [], [] when acc = [] -> None
    | [], [] -> Some (Record (List.rev acc))
    | [], tail -> make_tail (fun kv -> New_in_updated (recf kv)) tail acc
    | tail, [] -> make_tail (fun kv -> Not_in_updated (recf kv)) tail acc
    | (((k_o, v_o) as h_o) :: t_o as l_o), (((k_u, v_u) as h_u) :: t_u as l_u) ->
        let c = String.compare k_o k_u in
        if c = 0 then
          match of_sexps ~original:v_o ~updated:v_u with
          | None -> of_record_fields acc t_o t_u
          | Some diff -> of_record_fields (Bad_match (k_u, diff) :: acc) t_o t_u
        else if c > 0 then of_record_fields (New_in_updated (recf h_u) :: acc) l_o t_u
        else of_record_fields (Not_in_updated (recf h_o) :: acc) t_o l_u

  and of_lists acc original updated =
    match original, updated with
    | [], [] when acc = [] -> None
    | [], [] -> Some (List (List.rev acc))
    | [], _ | _, [] -> assert false  (* impossible *)
    | h_orig :: t_orig, h_upd :: t_upd ->
        match of_sexps ~original:h_orig ~updated:h_upd with
        | None -> of_lists acc t_orig t_upd
        | Some res -> of_lists (res :: acc) t_orig t_upd

  and of_sexps ~original ~updated =
    match original, updated with
    | Sexp.List [], Sexp.List [] -> None
    | Sexp.Atom a1, Sexp.Atom a2 when a1 = a2 -> None
    | Sexp.List orig, Sexp.List upd ->
        if maybe_record orig && maybe_record upd then
          of_record_fields [] (sort_record_fields orig) (sort_record_fields upd)
        else if List.length orig = List.length upd then of_lists [] orig upd
        else Some (Different (`Original original, `Updated updated))
    | _ -> Some (Different (`Original original, `Updated updated))

  let to_buffer diff =
    let buf = Buffer.create 80 in
    let print_string ~tag ~indent str =
      Buffer.add_string buf (Printf.sprintf "%-*s %s\n%!" indent tag str)
    in
    let print_sexp ~tag ~indent sexp =
      print_string ~tag ~indent (Sexp.to_string sexp)
    in
    let rec loop indent = function
      | Different (`Original sexp1, `Updated sexp2) ->
        print_sexp ~tag:"-" ~indent sexp1;
        print_sexp ~tag:"+" ~indent sexp2
      | List lst ->
        print_string ~tag:"" ~indent "(";
        List.iter (loop (indent + 1)) lst;
        print_string ~tag:"" ~indent ")"
      | Record record_fields ->
        let print_record_field = function
          | New_in_updated sexp -> print_sexp ~tag:"+" ~indent sexp
          | Not_in_updated sexp -> print_sexp ~tag:"-" ~indent sexp
          | Bad_match (key, diff) ->
            print_string ~tag:"" ~indent key;
            loop (indent + 1) diff
        in
        List.iter print_record_field record_fields;
    in
    loop 0 diff;
    buf

  let to_string diff = Buffer.contents (to_buffer diff)

  let print ?(oc = Pervasives.stdout) diff = Buffer.print (IO.output_channel oc) (to_buffer diff)
end

open Modelica_parser
open Syntax_fragments
open Modelica_lexer
open Location
open Parser_tests

open Modlib
open Modlib.Syntax
open Modlib.Inter
open Modlib.NormImpl
open Modlib.Normalized
open Modlib.Report
open Modlib.Utils

let diff_sexp f fmt (e1, e2) =
  match Diff.of_sexps ~original:(f e1) ~updated:(f e2) with Some d -> Format.fprintf fmt "%s\n" (Diff.to_string d) | None -> ()

let diff_exp = diff_sexp sexp_of_exp

let diff_eq = diff_sexp sexp_of_equation

let diff_st = diff_sexp sexp_of_statement

let cm = Modlib.Inter.Path.cm

module ClassValueFragments = struct
  let empty object_sort source_path = (Class {empty_object_struct with object_sort; source_path })                                               

  let type_ arg = Constr {constr=Sort Syntax.Flags.Type; arg}

  let const arg = Constr {constr=Var Syntax.Flags.Constant; arg}

  let real = Real

  let int = Int

  let real_t = type_ real

  let int_t = type_ int
  
  let replaceable t = Replaceable t

  let sup n = `SuperClass n

  let cl x = `ClassMember x

  let fld x = `FieldType x

  let cl_path xs = DQ.of_list (List.map cl xs)

  let dynref upref downref = DynamicReference {upref;base=false;downref}
end

module P = struct
  (** 'Speaking' test combinators *)
  
  let ( **>) p1 p2 = p1 p2 
  let (&&&) p1 p2 got = (p1 got) ; (p2 got)

  let public = true
  
  module Points = struct
    let to_ k = function
        GlobalReference p -> k p
      | Class os -> k os.source_path
      | cv -> assert_failure ("Expected a reference or a class, got: " ^ (show_class_value cv))
  end

  module ElementsStruct = struct
    let has_class_member name k {class_members} =
      if StrMap.mem name class_members then
        k (StrMap.find name class_members)
      else
        assert_failure ("No class named '" ^ name ^ "'")          
  end
  
  module Ensure = struct 
    module Report = struct
      let show_messages msgs =
        let s = IO.output_string () in
        Modlib.Report.print_messages s msgs ; IO.close_out s

      let has_no_messages k ({final_messages} as report) = 
        assert_equal ~msg:"No warnings and errors expected" ~printer:show_messages [] final_messages (* TODO: filter warnings / errors *) ;
        k report
    
      let result k {final_result} = k final_result
    end    
  end

  module Find = struct
    let component cs k got = match cs with
        [] -> raise (Failure "empty name for lookup")
      | c::cs ->
        let open ModlibLookup in 
        k (lookup_continue (state_of_lib got) c cs)
    
    (* Lookup name and flatten attributes *)
    let def_of path cs k got =
      let open ModlibLookup in
      let state = forward_state (state_of_lib got) path in
      k (lookup_continue_or_yield state cs)

    let class_at path k got =
      let open ModlibLookup in
      let state = forward_state (state_of_lib got) path in
      k (Class state.self.tip.clbdy)

    let type_at path k got =
      match (lookup_path_direct got path) with `Found {found_value} -> k found_value | _ -> assert_failure "Cannot find path"
    
  end

  module Has = struct

    let annotation a k = function
      | Class {annotation=Some m} when StrMap.mem a m.mod_nested -> k (StrMap.find a m.mod_nested)
      | cv -> assert_failure ("No annotation '" ^ a ^ "' on: " ^ (show_class_value cv)) 
    
    let class_member vis cm k = function
      | Class {public} when vis && StrMap.mem cm public.class_members -> k (StrMap.find cm public.class_members)
      | Class {protected} when (not vis) && StrMap.mem cm protected.class_members -> k (StrMap.find cm protected.class_members)
      | cv -> assert_failure ("No class: '"^cm^"' in: " ^ (show_class_value cv)) 

    let field vis fld k = function
      | Class {public} when vis && StrMap.mem fld public.fields -> k (StrMap.find fld public.fields)
      | Class {protected} when (not vis) && StrMap.mem fld protected.fields -> k (StrMap.find fld protected.fields)
      | cv -> assert_failure ("No field: '"^fld^"' in: " ^ (show_class_value cv)) 

    let super_class vis n k = function
      | Class {public} when vis && IntMap.mem n public.super -> k (IntMap.find n public.super)
      | Class {protected} when (not vis) && IntMap.mem n protected.super -> k (IntMap.find n protected.super)
      | cv -> assert_failure ("No Super Class: '"^(string_of_int n)^"' in: " ^ (show_class_value cv)) 

    let field_type k = function
      {field_class} -> k field_class
    
    let binding k = function
        {field_mod={mod_default=Some b}} -> k b
      | _ -> assert_failure "Expected a binding"

    let class_modification fld k {class_mod} =
      if StrMap.mem fld class_mod then
        k (StrMap.find fld class_mod)
      else
        assert_failure ("No modification to '" ^ fld ^ "'")  

    let super_class_modification fld k {super_mod} =
      if StrMap.mem fld super_mod then
        k (StrMap.find fld super_mod)
      else
        assert_failure ("No modification to '" ^ fld ^ "'")  
    
    let modification fld k {field_mod} =
      if StrMap.mem fld field_mod.mod_nested then
        k (StrMap.find fld field_mod.mod_nested)
      else
        assert_failure ("No modification to '" ^ fld ^ "'")  

    let modification_kind kind m =
      assert_equal ~printer:show_component_kind kind m.mod_kind

    let element x k m =
      if StrMap.mem x m then
        k (StrMap.find x m)
      else        
        assert_failure ("No element '" ^ x ^ "'" )

    let equations k {equations} = k equations

    let algorithms k {algorithms} = k algorithms
    
    let behavior k = function
      Class {behavior} -> k behavior
    | cv -> assert_failure ("Expected a class. Got: " ^ (show_class_value cv))
      
  end

  module The = struct
    open ModlibLookup
    let first k = function [] -> assert_failure "Expected non-empty list" | x :: _ -> k x

    let lookup_result k {lookup_success_value; lookup_success_state={current_attr}} =
      let cv = unflat (extract_attributes current_attr (Lookup.class_value_of_lookup lookup_success_value)) in
      k cv

    let declared_class k {class_} = k class_

    let class_modification k {class_mod} = k class_mod
  end
  
  module Is = struct
    open ModlibLookup
    let path expected p =
      assert_equal ~cmp:Path.equal ~printer:Path.show expected p

    let rec valid_ctxt_for path = function
      [] -> assert_equal ~printer:Inter.Path.show DQ.empty path
      | ctxt::ctxts -> begin match DQ.rear path with
          | Some(xs,x) ->
            (* Contexts are in bottom-up-order *)
            assert_equal ~cmp:Inter.Path.equal ~printer:Inter.Path.show ctxt.source_path path ;
            valid_ctxt_for xs ctxts
          | None -> assert_failure ("End of path reached, but context non-empty: " ^ Inter.Path.show ctxt.source_path)
        end

    let successful k = function
        Success s -> k s
      | Error err -> assert_failure ("Lookup Error: " ^ (show_components err.lookup_error_todo))
    
    let ok k = function
        Failed -> assert_failure "Result was not OK."
      | Ok a -> k a

    let constant k = function
        Constr {arg; constr=Var Flags.Constant} -> k arg
      | got -> assert_failure ("Expected a constant type, got: " ^ (show_class_value got))
    
    let replaceable k = function
        Replaceable v -> k v
      | got -> assert_failure ("Expected a replaceable type, got: " ^ (show_class_value got))
    
    let erase_location = ModlibNormalized.cv_mapper ~map_expr:Parser_tests.prep_expr ()
                                                           
    let prep = erase_location.map_class_value erase_location

    let class_value expected got =
      assert_equal ~cmp:equal_class_value ~msg:(Printf.sprintf "equality of normalization result = %b" (expected = got)) ~printer:show_class_value (norm_cv expected) (norm_cv got)

    let exp expected got =
      assert_equal ~printer:show_exp ~pp_diff:diff_exp ~cmp:Syntax.equal_exp expected (Parser_tests.prep_expr got)

    let bound_to e =
      Has.binding (exp e)

    let nested k {mod_nested} = k mod_nested

    let modified_to expected = function
        {mod_default=Some e} -> exp expected e
      | _ -> assert_failure "Expected a binding modification."

    let equal_to_modification expected = 
      assert_equal ~printer:(StrMap.show pp_field_modification) ~cmp:(StrMap.eq equal_field_modification) expected 
    
    let equation expected eq =
      assert_equal ~cmp:equal_equation ~pp_diff:diff_eq ~printer:show_equation expected (Parser_tests.prep_eq eq)

    let statement expected st =
      assert_equal ~cmp:equal_statement ~pp_diff:diff_st ~printer:show_statement expected (Parser_tests.prep_stmt st)
    
  end

  module Compute = struct
    open FileSystem
        
    let signature (k : elements_struct -> unit) td = 
      let parsed = {within = Some []; toplevel_defs = [td] } in
      let report =
        (Modlib.Report.run (NormSig.norm_pkg_root
                              (Trans.translate_pkg_root {root_units=[{scanned="testcase"; parsed}];root_packages=[]} ))
           {messages=[]; output=empty_elements})
      in
      (Ensure.Report.has_no_messages **> Ensure.Report.result **> Is.ok **> k) report

    let implementation (k : elements_struct -> unit) td = 
      let parsed = {within = Some []; toplevel_defs = [td] } in
      let report =
        (Modlib.Report.run (NormLib.norm_pkg_root (Trans.translate_pkg_root {root_units=[{FileSystem.scanned="testcase"; parsed}];root_packages=[]} )) {messages=[]; output=empty_elements})
      in
      (Ensure.Report.has_no_messages **> Ensure.Report.result **> Is.ok **> (fun {NormLib.implementation} -> k implementation)) report
  end
  
  module Parse = struct
    let parse parser k input = 
      let ucs = state_from_utf8_string "test input" input in
      let next () = next_token ucs in
      let last () = last_token ucs in
      fun _ ->
        try
          k (parser next last)
        with 
          SyntaxError e -> assert_failure (Printf.sprintf "Syntax Error at %s:\n%s" (show_location e) (error_message e input))

    let as_typedef = parse Parser.td_parser
  end
end

let nl = Location.mknoloc

open P

(*let test_env descr input classname expected =
  descr >:: ( (Parse.as_typedef **> Compute.signature **> Compute.env_of (Path.of_list classname) **> (Is.env expected)) input)*)

let test_norm descr input classname pred =
  descr >:: (Parse.as_typedef **> Compute.implementation **> Find.class_at (Path.of_list classname) **> pred) input
