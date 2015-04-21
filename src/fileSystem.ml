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

type scanned = string
type parsed = {scanned : scanned ; parsed : Syntax.unit_}
       
type 'stage package = {
  pkg_name : string list;
  sub_packages : ('stage package) list ;
  external_units : 'stage list;
  package_unit : 'stage;
}

type 'stage pkg_root = {
    root_units : 'stage list ;
    root_packages : 'stage package list;
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
                 
let is_source_file file = String.ends_with (Filename.basename file) ".mo" 

let is_package_mo file = (Filename.basename file) = "package.mo" 
                                                                            
let rec scan prefix dir =
  if is_directory dir then
    let pkg_name = (Filename.basename dir)::prefix in
    let contents = (Array.to_list (Array.map (Filename.concat dir) (Sys.readdir dir))) in

    (* we could do this as well in one fold over the content of the directory, but this is more readable *)
    if List.exists is_package_mo contents then 

      let package_unit = List.find is_package_mo contents in
      let collect_sub_pkg pkgs file = match scan pkg_name file with None -> pkgs | Some pkg -> pkg::pkgs in
      let collect_source_files files file = if (is_source_file file) && not (is_package_mo file) then file::files else files in
        
      let sub_packages = List.fold_left collect_sub_pkg [] contents in
      let external_units = List.fold_left collect_source_files [] contents in      
      Some { package_unit ; pkg_name ; sub_packages ; external_units }
    else None
    
  else None

let scan_root dir =
  if is_directory dir then
    let contents = Array.to_list (Array.map (Filename.concat dir) (Sys.readdir dir)) in
    
    let collect_sub_pkg pkgs file = match scan [dir] file with None -> pkgs | Some pkg -> pkg::pkgs in
    let collect_source_files files file = if (is_source_file file) && not (is_package_mo file) then file::files else files in

    let root_packages = List.fold_left collect_sub_pkg [] contents in
    let root_units = List.fold_left collect_source_files [] contents in
    {root_units; root_packages}
  else {root_units = []; root_packages = []}

let rec parse_externals done_ = function
    [] -> Some done_
  | scanned::fs -> begin match parse scanned with
                         | Some parsed -> parse_externals ({scanned;parsed}::done_) fs
                         | None -> None
                   end
    
let rec parse_package {pkg_name; package_unit=scanned; external_units; sub_packages } =
  match parse_packages [] sub_packages with
    Some sub_packages -> begin
      match parse_externals [] external_units with
        Some external_units -> begin
          match parse scanned with
            Some parsed -> Some {pkg_name; package_unit={scanned; parsed}; external_units; sub_packages}
          | None -> None
        end
      | None -> None
    end
  | None -> None
  
and parse_packages done_ = function
    [] -> Some done_
  | pkg::pkgs -> begin 
      match parse_package pkg with Some pkg -> parse_packages (pkg::done_) pkgs
                                 | None -> None
    end
    
let rec parse_root {root_units; root_packages} =  
  match parse_packages [] root_packages with
    Some root_packages -> begin match parse_externals [] root_units with
                                  Some root_units -> Some {root_units; root_packages}
                                | None -> None
                          end
  | None -> None
                                              
