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
open Utils
open ModlibNormalized
open ModlibLookup
open Syntax
    
type level = Info | Warning | Error [@@deriving show]

type 'a result = Ok of 'a | Failed

type message = { level : level ; where : Location.t ; what : string }

let show_loc loc =
  Location.print Format.str_formatter loc ; Format.flush_str_formatter ()

let show_message {level;where;what} = if where != Location.none then
    Printf.sprintf "%s\n%s: %s" (show_loc where) (show_level level) what 
    else Printf.sprintf "%s: %s" (show_level level) what

let print_message o msg = IO.nwrite o (show_message msg)

let print_messages o msgs = List.print ~sep:"\n" print_message o msgs

type state = { messages : message list; output : elements_struct }

type 'a report = { result : 'a result ; state : state }

type 'a final_report = { final_result : 'a result ; final_messages : message list }

let run m state = let {result;state} = m state in
  {final_result=result; final_messages=state.messages}

let bind m f state = let {state;result} = m state in
  match result with Failed -> {state;result=Failed}
                  | Ok a -> f a state

let return a state = {state ; result = Ok a}

let rec miter f = function
    [] -> return ()
  | x::xs ->     
    bind (f x) (fun () -> miter f xs)

let rec on_sequence f = function
  (* TODO: tail_recursion *)
    [] -> return []
  | x::xs ->
    bind (f x) (fun x' -> (bind (on_sequence f xs) (fun xs' -> (return (x'::xs') ) )  ) )

let rec fold m a = function
    [] -> return a
  | x::xs -> do_ ; a' <-- (m a x) ; fold m a' xs

let on_kv_pair f (k,v) = do_ ; v' <-- f v ; return (k,v')

let on_strMap_values f map = do_ ;
  xs <-- on_sequence (on_kv_pair f) (StrMap.bindings map) ;
  return (StrMap.of_list xs)

let on_intMap_values f map = do_ ;
  xs <-- on_sequence (on_kv_pair f) (IntMap.bindings map) ;
  return (IntMap.of_list xs)


let output ({output} as state) = {result = Ok output; state }

let set_output output state = {result = Ok (); state={state with output}}

let messages ({messages} as state) = {result=Ok messages; state}

let log msg state = {state={state with messages = msg::state.messages}; result=Ok ()}

let fail state = {state; result=Failed}

let if_ b m = if b then m else return ()

type unresolved_dependency = { searching : Name.t ; result : search_error }

let fail_unresolved {searching; result} =
  do_ ;
  log{level=Error;where=Location.none;
      what=Printf.sprintf "Dependency %s not evaluated:\n%s\n"
          (Name.show searching)
          (show_search_error result)} ;
  fail

let fail_lookup {lookup_error_state=state; lookup_error_todo=todo} =
  do_ ;
  log{level=Error;where=(match todo with [] -> Location.none | fst::_ -> fst.ident.loc);
      what=Printf.sprintf "Could not find %s in:\n%s\n"
          (show_components todo)
          (dump_lookup_state state)} ;
  fail
