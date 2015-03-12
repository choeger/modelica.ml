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
open Class_deps
open ClassNorm
open Motypes
open Report
open Utils
open Batteries
open Location
       
let stats u =
  let {def_count; type_count} = generate_stats u in
  Printf.printf "Component Definitions: %d\nType Definitions: %d\n" def_count type_count  
                                             
let normalize u = match u.toplevel_defs with
    d::_ -> ClassNorm.normalize d
  | _ -> {final_messages = []; final_result= Ok Normalized.empty_class_body}

let print_message msg = Printf.printf "%s\n" (show_message msg)
  
let _ =
  Format.pp_set_margin Format.str_formatter (140);
  match (scan [] argv.(1)) with
    Some pkg ->  begin match merge pkg with Some u ->
                                            let hier = normalize u in
                                            Printf.printf "%d messages.\n" (List.length hier.final_messages) ;
                                            List.iter print_message hier.final_messages ;                                              
                                            0
                                          | None -> 1 end
  | None -> Printf.eprintf "'%s' does not seem to be a Modelica package.\n" argv.(1) ; 1
              
                  
