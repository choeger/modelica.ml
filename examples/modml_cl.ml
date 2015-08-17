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

open Sys
open FileSystem
open Pprint_modelica
open Stats
open Syntax
open Motypes
open Utils
open Batteries
open ClassTrans
open ClassDeps
open ClassNorm
open Report
open Location
       
let print_message msg = BatLog.logf "%s\n" (show_message msg)

open Normalized

let _ =
  StdFormat.pp_set_margin StdFormat.str_formatter (240);
  match (scan_root argv.(1)) with
  | {root_units = []; root_packages = []} -> Printf.eprintf "'%s' seems to contain no Modelica content.\n" argv.(1) ; 1
  | root -> begin match parse_root root with
                    Some root -> begin 
                      let tr = translate_pkg_root root in
                      let o = run (norm_pkg_root tr) {messages=[]; output=empty_elements} in
                      List.iter print_message o.final_messages ;
                      match o.final_result with
                        Ok o -> BatLog.logf "Normalization Ok.\n%!" ;
                                let c = compress_elements o in
                                BatLog.logf "Compression Ok.\n%!" ;
                                let js = elements_struct_to_yojson c in
                                let dump = Yojson.Safe.pretty_to_string js in
                                BatLog.logf "Dump (%d) Ok.\n" (String.length dump);
                                Printf.printf "%s\n" dump ;
                                0
                      | Failed -> BatLog.logf "Normalization Error\n" ; 1 
                    end 
                  | None -> BatLog.logf "Syntax Error\n" ; 1
            end            
