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

open Batteries
open Modelica_lexer
open Modelica_parser
open Syntax
open Sys
open Utils
       
type package = {
  pkg_name : string list;
  sub_packages : package list ;
  source_files : string list;
  package_mo : string;
}

type pkg_root = {
    root_files : string list ;
    root_packages : package list;
  }
                 
let parse file =
  begin
    try
      begin
        let input = IO.read_all (File.open_in file) in
        try
          let ucs = state_from_utf8_string file input in
          let next () = next_token ucs in
          let last () = last_token ucs in
          let result = (unit_parser next last) in
          Some result                              
        with
        | SyntaxError e -> Printf.eprintf "Syntax Error at %s:\n%s" (show_location e) (error_message e input) ;
                           None
      end
    with
    | Sedlexing.MalFormed -> Printf.eprintf "Lexical error in %s\n" file ;
                             None

  end

                 
let package_name { pkg_name } = pkg_name
                 
let package_mo { package_mo } = package_mo
                                  
let sub_packages { sub_packages } = sub_packages
                                      
let source_files { source_files } = source_files

let is_source_file file = String.ends_with (Filename.basename file) ".mo" 

let is_package_mo file = (Filename.basename file) = "package.mo" 
                                                                            
let rec scan prefix dir =
  if is_directory dir then
    let pkg_name = (Filename.basename dir)::prefix in
    let contents = (Array.to_list (Array.map (Filename.concat dir) (Sys.readdir dir))) in

    (* we could do this as well in one fold over the content of the directory, but this is more readable *)
    if List.exists is_package_mo contents then 

      let package_mo = List.find is_package_mo contents in
      let collect_sub_pkg pkgs file = match scan pkg_name file with None -> pkgs | Some pkg -> pkg::pkgs in
      let collect_source_files files file = if (is_source_file file) && not (is_package_mo file) then file::files else files in
        
      let sub_packages = List.fold_left collect_sub_pkg [] contents in
      let source_files = List.fold_left collect_source_files [] contents in      
      Some { package_mo ; pkg_name ; sub_packages ; source_files }
    else None
    
  else None

let scan_root dir =
  if is_directory dir then
    let contents = Array.to_list (Array.map (Filename.concat dir) (Sys.readdir dir)) in
    
    let collect_sub_pkg pkgs file = match scan [dir] file with None -> pkgs | Some pkg -> pkg::pkgs in
    let collect_source_files files file = if (is_source_file file) && not (is_package_mo file) then file::files else files in

    let root_packages = List.fold_left collect_sub_pkg [] contents in
    let root_files = List.fold_left collect_source_files [] contents in
    {root_files; root_packages}
  else {root_files = []; root_packages = []}

let merge_source_file tds file =
  match parse file with
  | Some { within ; toplevel_defs = tl::_ } -> tl::tds 
  | _ -> tds
         
let rec merge { package_mo ; source_files ; sub_packages } =
 
  match parse package_mo with
    Some { within ; toplevel_defs = {commented=Composition (comp as p); comment}::_ } ->
    let tds = comp.type_exp.public.typedefs in
    let tds' = List.fold_left merge_source_file tds source_files in
    let tds'' = List.fold_left merge_sub_pkg tds' sub_packages in
    let p' = {p with type_exp = {p.type_exp with public = {p.type_exp.public with typedefs = tds''}}} in
    Some { within ; toplevel_defs = [{commented=Composition p';comment}]} 
  | _ -> None

and merge_sub_pkg tds pkg =
  match merge pkg with
    Some { within ; toplevel_defs = p::_ } -> p::tds
  | _ -> tds

let rec merge_root {root_files; root_packages} =
  let pkg_tds = List.fold_left merge_sub_pkg [] root_packages in
  let toplevel_defs = List.fold_left merge_source_file pkg_tds root_files in
  { within = None ; toplevel_defs }
