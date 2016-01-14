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
    let field vis fld k = function
      | Class {public} when vis && StrMap.mem fld public.fields -> k (StrMap.find fld public.fields)
      | Class {protected} when (not vis) && StrMap.mem fld protected.fields -> k (StrMap.find fld protected.fields)
      | cv -> assert_failure ("No field: '"^fld^"' in: " ^ (show_class_value cv)) 

    let binding k = function
        {field_binding=Some b} -> k b
      | _ -> assert_failure "Expected a binding"

    let modification fld k {field_mod} =
      if StrMap.mem fld field_mod then
        k (StrMap.find fld field_mod)
      else
        assert_failure ("No modification to '" ^ fld ^ "'")  

    let modification_kind kind m =
      assert_equal ~printer:show_component_kind kind m.mod_kind

  end
  
  module Is = struct
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
      assert_equal ~printer:show_exp ~cmp:Syntax.equal_exp expected got

    let bound_to e =
      Has.binding (exp e)

    let modified_to expected = function
        {mod_desc=Modify e} -> exp expected e
      | _ -> assert_failure "Expected a binding modification."
    
  end

  module Compute = struct
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

let assert_cm vis cm pred = function
  | Class {public} when vis && StrMap.mem cm public.class_members -> pred (StrMap.find cm public.class_members)
  | Class {protected} when (not vis) && StrMap.mem cm protected.class_members -> pred (StrMap.find cm protected.class_members)
  | cv -> assert_failure ("No class: '"^cm^"' in: " ^ (show_class_value cv)) 
  
let class_member = assert_cm

let has_equation eq = function
    Class {behavior} -> assert_equal ~printer:(show_list show_equation) ~cmp:(equal_list Syntax.equal_equation) [eq] (List.map Parser_tests.prep_eq behavior.equations)
  | cv -> assert_failure ("Expected a class. Got: " ^ (show_class_value cv))
    
let has_class_modification fld pred {class_mod} =
  assert_modification fld pred class_mod

let is_nested p m = match m.mod_desc with Nested m -> p m
                                        | Modify e -> assert_failure ("Expected a nested modification, got binding = %s" ^ (show_exp e))

let modified_element = assert_modification 


*)
