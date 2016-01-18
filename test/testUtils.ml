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
    
let cm = Modlib.Inter.Path.cm

module ClassValueFragments = struct
  let empty object_sort source_path = (Class {empty_object_struct with object_sort; source_path })                                               

  let type_ arg = Constr {constr=Sort Type; arg}

  let const arg = Constr {constr=Var Constant; arg}

  let real = type_ Real

  let int = type_ Int

  let real_t = real

  let replaceable t = Replaceable t

  let sup n = `SuperClass n

  let cl x = `ClassMember x

  let fld x = `FieldType x

  let cl_path xs = DQ.of_list (List.map cl xs)

  let dynref x = DynamicReference x
end

module P = struct
  (** 'Speaking' test combinators *)
  
  let ( **>) p1 p2 = p1 p2 
  let (&&&) p1 p2 got = (p1 got) ; (p2 got)

  
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
    (* Lookup a name and flatten attributes *)
    let rec def_of path k got =
      match DQ.front path with
        Some (x,xs) -> begin
          let rec def_of_ x xs k got =          
            let m = try Normalized.follow_path_es got Name.empty got xs x
              with IllegalPath i -> assert_failure ("Illegal path: " ^ i)
            in 
            match m with
            | `Found {found_value} ->
              begin match flat found_value with
                  {flat_val = GlobalReference n; flat_attr} -> 
                  begin match DQ.front n with
                    (* In case of a global reference, lookup the reference and remember all local attributes *)
                      Some (x,xs) -> let k' = fun flat_val -> k (unflat {flat_val; flat_attr}) in
                      def_of_ x xs k' got
                    | None -> assert_failure
                                (Printf.sprintf "Empty global reference when looking up %s" (Inter.Path.show (DQ.cons x xs)))
                  end
                (* In any other case, apply the predicate *)
                | _ -> k found_value
              end
            | _ as result -> assert_failure (Printf.sprintf "Could not find test-path.\n%s\n %s\n" (show_search_result result) (show_elements_struct got))
          in def_of_ x xs k got
        end
      | None -> assert_failure "Cannot lookup empty path"
  end

  module Has = struct

    let class_member vis cm k = function
      | Class {public} when vis && StrMap.mem cm public.class_members -> k (StrMap.find cm public.class_members)
      | Class {protected} when (not vis) && StrMap.mem cm protected.class_members -> k (StrMap.find cm protected.class_members)
      | cv -> assert_failure ("No class: '"^cm^"' in: " ^ (show_class_value cv)) 

    let field vis fld k = function
      | Class {public} when vis && StrMap.mem fld public.fields -> k (StrMap.find fld public.fields)
      | Class {protected} when (not vis) && StrMap.mem fld protected.fields -> k (StrMap.find fld protected.fields)
      | cv -> assert_failure ("No field: '"^fld^"' in: " ^ (show_class_value cv)) 

    let binding k = function
        {field_binding=Some b} -> k b
      | _ -> assert_failure "Expected a binding"

    let class_modification fld k {class_mod} =
      if StrMap.mem fld class_mod then
        k (StrMap.find fld class_mod)
      else
        assert_failure ("No modification to '" ^ fld ^ "'")  
    
    let modification fld k {field_mod} =
      if StrMap.mem fld field_mod then
        k (StrMap.find fld field_mod)
      else
        assert_failure ("No modification to '" ^ fld ^ "'")  

    let modification_kind kind m =
      assert_equal ~printer:show_component_kind kind m.mod_kind

    let element x k m =
      if StrMap.mem x m then
        k (StrMap.find x m)
      else        
        assert_failure ("No element '" ^ x ^ "'")

    let equations k {equations} = k equations
    
    let behavior k = function
      Class {behavior} -> k behavior
    | cv -> assert_failure ("Expected a class. Got: " ^ (show_class_value cv))
      
  end

  module The = struct
    let first k = function [] -> assert_failure "Expected non-empty list" | x :: _ -> k x
  end
  
  module Is = struct
    let struct_val expected p =
      assert_equal ~printer:show_struct_val expected p

    let path expected p =
      assert_equal ~cmp:Path.equal ~printer:Path.show expected p

    let env expected env =
      assert_equal ~printer:show_environment expected env

    let lexical_env expected env =
      assert_equal ~cmp:equal_lexical_env ~printer:show_lexical_env expected env
        
    let rec valid_ctxt_for path = function
      [] -> assert_equal ~printer:Inter.Path.show DQ.empty path
      | ctxt::ctxts -> begin match DQ.rear path with
          | Some(xs,x) ->
            (* Contexts are in bottom-up-order *)
            assert_equal ~cmp:Inter.Path.equal ~printer:Inter.Path.show ctxt.source_path path ;
            valid_ctxt_for xs ctxts
          | None -> assert_failure ("End of path reached, but context non-empty: " ^ Inter.Path.show ctxt.source_path)
        end
    
    let ok k = function
        Failed -> assert_failure "Result was not OK."
      | Ok a -> k a

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

    let nested k = function
        {mod_desc=Nested m} -> k m
      | _ -> assert_failure "Expected a nested modification."

    let modified_to expected = function
        {mod_desc=Modify e} -> exp expected e
      | _ -> assert_failure "Expected a binding modification."

    let equation expected eq =
      assert_equal ~cmp:equal_equation ~pp_diff:diff_eq ~printer:show_equation expected (Parser_tests.prep_eq eq)
    
  end

  module Compute = struct
    let structural_type_of p k public =
      k (Normalized.eval_struct (DQ.snoc DQ.empty {up=None; tip={empty_object_struct with public}}) (GlobalReference p))

    let signature (k : elements_struct -> unit) td = 
      let parsed = {within = Some []; toplevel_defs = [td] } in
      let report =
        (Modlib.Report.run (NormSig.norm_pkg_root (Trans.translate_pkg_root {root_units=[{FileSystem.scanned="testcase"; parsed}];root_packages=[]} )) {messages=[]; output=empty_elements})
      in
      (Ensure.Report.has_no_messages **> Ensure.Report.result **> Is.ok **> k) report

    let implementation (k : elements_struct -> unit) td = 
      let parsed = {within = Some []; toplevel_defs = [td] } in
      let report =
        (Modlib.Report.run (NormLib.norm_pkg_root (Trans.translate_pkg_root {root_units=[{FileSystem.scanned="testcase"; parsed}];root_packages=[]} )) {messages=[]; output=empty_elements})
      in
      (Ensure.Report.has_no_messages **> Ensure.Report.result **> Is.ok **> (fun {NormLib.implementation} -> k implementation)) report

    let env_of path k lib =
        Find.def_of path (fun cl -> k (env lib cl)) lib

      let lexical_ctxt_of path k lib =
        k (lexical_ctxt lib path).ctxt_classes
        
      let lexical_env_of path k lib =
        k (lexical_env lib path)
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

let test_env descr input classname expected =
  descr >:: ( (Parse.as_typedef **> Compute.signature **> Compute.env_of (Path.of_list classname) **> (Is.env expected)) input)

let test_ctxt descr input classname =
  descr >:: (Parse.as_typedef **> Compute.signature **> Compute.lexical_ctxt_of (Path.of_list classname) **> (Is.valid_ctxt_for (Path.of_list classname))) input

let test_lex_env descr input classname expected =
  descr >:: (Parse.as_typedef **> Compute.signature **> Compute.lexical_env_of (Path.of_list classname) **> (Is.lexical_env expected)) input

let test_norm descr input classname pred =
  descr >:: (Parse.as_typedef **> Compute.implementation **> Find.def_of (Path.of_list classname) **> pred) input

let t = test_env "Empty class" "class A end A" [`ClassMember "A"] NormImpl.empty_env ;

             (*


let field = assert_fld

let class_member = assert_cm

    
let modified_element = assert_modification 

*)
