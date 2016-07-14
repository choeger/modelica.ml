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
open Unix
open Modelica_parser
open Modelica_lexer
open Syntax       
open Syntax_fragments

let hidden dir = String.starts_with (Filename.basename dir) "."

let erase_location = { identity_mapper with map_loc_t = (fun _ _ -> Location.none) }

let parse file =
  let start = Sys.time () in
  begin
    try
      begin
        let input = IO.read_all (File.open_in file) in
        try
          let ucs = state_from_utf8_string file input in
          let next () = next_token ucs in
          let last () = last_token ucs in
          let result = (unit_parser next last) in
          ANSITerminal.printf [ANSITerminal.green] "%fs parsing: '%s'\n" (Sys.time () -. start) file ;
          (*let pp = Pprint_modelica.unit2str result in
          let ucs = state_from_utf8_string file input in
          let next () = next_token ucs in
          let last () = last_token ucs in
          begin
          try 
            let result' = (unit_parser next last) in            
            let result_noloc = erase_location.map_unit_ erase_location result in
            let result'_noloc = erase_location.map_unit_ erase_location result' in

            if not (result_noloc = result'_noloc) then begin
              ANSITerminal.printf [ANSITerminal.red] "parsing != unparsing '%s'\n" file ;
              Printf.printf "%s\n%s\n" (show_unit_ result_noloc) (show_unit_ result'_noloc) ;
            end ;
          *)
            Some result
          (*with 
          | Sedlexing.MalFormed -> Printf.eprintf "Lexical error in unparse of %s\n" file ;
            ANSITerminal.printf [ANSITerminal.red] "%fs parsing: '%s'\n" (Sys.time () -. start) file ;
            None
          | SyntaxError e ->
            Printf.eprintf "Syntax Error in unparse at %s:\n%s" (show_location e) (error_message e input) ;
            ANSITerminal.printf [ANSITerminal.red] "%fs re-parsing: '%s'\n" (Sys.time () -. start) file ;
            None
            end*)
        with
        | SyntaxError e -> Printf.eprintf "Syntax Error at %s:\n%s" (show_location e) (error_message e input) ;
                           ANSITerminal.printf [ANSITerminal.red] "%fs parsing: '%s'\n" (Sys.time () -. start) file ;
                           None
      end
    with
    | Sedlexing.MalFormed -> Printf.eprintf "Lexical error in %s\n" file ;
                             ANSITerminal.printf [ANSITerminal.red] "%fs parsing: '%s'\n" (Sys.time () -. start) file ;
                             None

  end
       
let walk_directory_tree dir suffix =
  let select str =
    String.ends_with str suffix
  in
  let rec walk acc = function
  | [] -> (acc)
  | dir::tail when not (hidden dir)->
      let contents = Array.to_list (Sys.readdir dir) in
      let contents = List.rev_map (Filename.concat dir) contents in
      let dirs, files =
        List.fold_left (fun (dirs,files) f ->
             match (stat f).st_kind with
             | S_REG -> (dirs, f::files)  (* Regular file *)
             | S_DIR -> (f::dirs, files)  (* Directory *)
             | _ -> (dirs, files)
          ) ([],[]) contents
      in
      let matched = List.filter (select) files in
      let acc' = matched @ acc in
      walk (acc') (dirs @ tail) 
  | dir::tail -> walk acc tail
  in
  walk [] [dir]
;;
  
let () =
  let results = walk_directory_tree (Sys.getcwd ()) ".mo" in
  ignore (List.map parse results);
  Gc.print_stat IO.stdout
;;
