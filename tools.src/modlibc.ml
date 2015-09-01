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

(** Compile a Modelica library into the normalized intermediate format *)

open Batteries
open Utils
open Modlib

let public_signatures = ref []
let inputs = ref []
let outfile = ref ""

let add_signature sign =
  public_signatures := sign :: (!public_signatures)

let add_input dir =
  inputs := dir :: (!inputs)

let args = [
  "-s" , Arg.String add_signature, "The signature of a library this library depends on." ;
  "-o", Arg.Set_string outfile, "The output file-name"
]

let print_message i msg = BatLog.logf "%d: %s\n" i (Report.show_message msg)

exception BadDependency of string

let load global dep =
  let js = Yojson.Safe.from_file dep in
  let o = Report.run (Compress.load_from_json js)
      {messages=[]; output=global}
  in
  List.iteri print_message o.final_messages ;
  match o.final_result with
    Ok global' -> global'
  | Failed -> raise (BadDependency dep)

let load_dependencies () =
  List.fold_left load Normalized.empty_elements !public_signatures 

let gather root input =
  let open FileSystem in
  let r = scan_root input in
  {root_units = root.root_units @ r.root_units ;
   root_packages = root.root_packages @ r.root_packages}

exception NoInput

let gather_sources () =
  let root = List.fold_left gather {root_units = []; root_packages = []} !inputs
  in
  match root with
    {root_units = []; root_packages = []} ->
    raise NoInput
  | root -> root

let run_compile global root =
  match FileSystem.parse_root root with
    Some root -> begin 
      let tr = Trans.translate_pkg_root root in
      let o = Report.run (NormSig.norm_pkg_root tr)
          {messages=[]; output=global} in
      List.iteri print_message o.final_messages ;
      match o.final_result with
        Ok o -> BatLog.logf "Normalization Ok.\n%!" ;
        let c = Compress.compress_elements o in
        BatLog.logf "Compression Ok.\n%!" ;
        let js = Normalized.elements_struct_to_yojson c in
        let dump = Yojson.Safe.pretty_to_string js in
        BatLog.logf "Dump (%d) Ok.\n" (String.length dump);
        let f = open_out !outfile in
        IO.nwrite f dump ;
        close_out f ;
        0
      | Failed -> BatLog.logf "Normalization Error\n" ; 1 
    end 
  | None -> BatLog.logf "Syntax Error\n" ; 1

let () =
  StdFormat.pp_set_margin StdFormat.str_formatter (240);
  Arg.parse args add_input "modlibc -o <OUTPUTFILE> -s <DEPENDENCY> <INPUTDIR>" ;
  let global_env = load_dependencies () in
  let src = gather_sources () in 
  let e = run_compile global_env src in
  exit e
    
