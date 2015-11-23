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
open Compress
    
let public_signatures = ref []
let inputs = ref []
let outfile = ref ""
let compress = ref false

let add_signature sign =
  public_signatures := sign :: (!public_signatures)

let add_input dir =
  inputs := dir :: (!inputs)

let args = [
  "-s" , Arg.String add_signature, "The signature of a library this library depends on." ;
  "-o", Arg.Set_string outfile, "The output file-name" ;
  "-c", Arg.Set compress, "Compress the output files" ;
]

let print_message i msg = BatLog.logf "%d: %s\n" i (Report.show_message msg)

exception BadDependency of string

let load global dep =
  BatLog.logf "Loading %s\n" dep ;
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

let clean global c =
  let open Normalized in
  let remove_cl k _ c = 
    BatLog.logf "Removing class %s\n" k ;
    {c with class_members = StrMap.remove k c.class_members}
  in
  (* remove the dependency parts *)
  StrMap.fold remove_cl global.class_members c

let sig_file () =
  if !compress then
    !outfile ^ ".modlib.csign"
  else
    !outfile ^ ".modlib.sign"

let impl_file () =
  if !compress then
    !outfile ^ ".modlib.cimpl"
  else
    !outfile ^ ".modlib.impl"

let write_out content filename =
  let f = open_out filename in
  (* TODO: compress *)
  IO.nwrite f content ;
  close_out f 
        
let run_compile global root =
  match FileSystem.parse_root root with
    Some root -> begin 
      let tr = Trans.translate_pkg_root root in
      let o = Report.run (NormLib.norm_pkg_root tr)
          {messages=[]; output=global} in
      List.iteri print_message o.final_messages ;
      match o.final_result with
        Ok {signature;implementation} -> BatLog.logf "Normalization Ok.\n%!" ;                
        let c = Compress.compress_elements signature in
        BatLog.logf "Compression Ok.\n%!" ;
        let c' = clean global c in
        
        let js = Normalized.elements_struct_to_yojson c' in
        let sig_dump = Yojson.Safe.pretty_to_string js in
        write_out sig_dump (sig_file ()) ;
        BatLog.logf "Signature Dump (%d) Ok.\n" (String.length sig_dump);

        let js = Normalized.elements_struct_to_yojson implementation in
        let impl_dump = Yojson.Safe.pretty_to_string js in
        write_out impl_dump (impl_file ()) ;
        BatLog.logf "Implementation Dump (%d) Ok.\n" (String.length impl_dump);

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
    
