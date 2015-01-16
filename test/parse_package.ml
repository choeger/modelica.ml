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
open Utils
open Batteries
       
let stats u =
  let {def_count; type_count} = generate_stats u in
  Printf.printf "Component Definitions: %d\nType Definitions: %d\n" def_count type_count  

let write_name o = List.print ~sep:"." IO.nwrite o
                
let name2str name =
  let o = IO.output_string () in
  write_name o name ; IO.close_out o

let from2str from =
  let o = IO.output_string () in
  List.print ~first:"{" ~sep:"|" ~last:"}" write_name o from ; IO.close_out o
                                                        
let print_dep { local_name ; from; element } =
  match element with
    [] -> Printf.printf "  '%s' from %s\n" local_name (from2str from)
  | es -> Printf.printf "  '%s (.%s)' from %s\n" local_name (name2str es) (from2str from)
                                                      
let print_def {global_name;dependencies} = Printf.printf "%d dependencies in %s\n" (List.length dependencies) (name2str global_name) ;
                                           List.iter print_dep dependencies 

let print_name global_name = Printf.printf "%s\n" (name2str global_name)
                                                     
let global_scope start = [{scope_name=[];scope_tainted=false;scope_entries=StrSet.singleton start}]

let name = function
    Short tds -> tds.td_name | Composition tds -> tds.td_name | Enumeration tds -> tds.td_name | OpenEnumeration tds -> tds.td_name | DerSpec tds -> tds.td_name | Extension tds -> tds.td_name
                                                     
let deps u = match u.toplevel_defs with
    d::_ -> let ldefs = Class_deps.scan_dependencies (global_scope (name d.commented)) d in
            List.iter print_def ldefs ;
            List.iter print_name (topological_order ldefs)
  | _ -> ()
                
let _ =
  Format.pp_set_margin Format.str_formatter (140);
  match (scan [] argv.(1)) with
    Some pkg ->  begin match merge pkg with Some u -> stats u ; deps u; (*Printf.printf "%s\n" (unit2str ~max:(max_int - 1) u);*) 0 | None -> 1 end
  | None -> Printf.eprintf "'%s' does not seem to be a Modelica package.\n" argv.(1) ; 1
              
                  
