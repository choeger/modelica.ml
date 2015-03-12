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

open Motypes
open Motypes.Normalized
open Utils
       
type level = Info | Warning | Error [@@deriving show]

type 'a result = Ok of 'a | Failed
                              
type message = { level : level ; where : Location.t ; what : string }

let show_message {level;what} = Printf.sprintf "%s: %s" (show_level level) what
                 
type state = { messages : message list; input : class_term ; output : Normalized.object_struct }
                 
type 'a report = { result : 'a result ; state : state }

type 'a final_report = { final_result : 'a result ; final_messages : message list }

let run m state = let {result;state} = m state in
                  {final_result=result; final_messages=state.messages}
                         
let bind m f state = let {state;result} = m state in
                     match result with Failed -> {state;result=Failed}
                                     | Ok a -> f a state

let return a state = {state ; result = Ok a}

let rec on_unit_sequence f = function
    [] -> return ()
  | x::xs ->
     do_ ; f x ; on_unit_sequence f xs
                       
let rec on_sequence f = function
    (* TODO: tail_recursion *)
    [] -> return []
  | x::xs ->
     bind (f x) (fun x' -> (bind (on_sequence f xs) (fun xs' -> (return (x'::xs') ) )  ) )
               
let on_kv_pair f (k,v) = do_ ; v' <-- f v ; return (k,v')
               
let on_strMap_values f map = do_ ;
                             xs <-- on_sequence (on_kv_pair f) (StrMap.bindings map) ;
                             return (StrMap.of_list xs)
                                  
let input ({input} as state) = {result = Ok input; state }
                                           
let output ({output} as state) = {result = Ok output; state }

let set_output output state = {result = Ok (); state={state with output}}
                                   
let messages ({messages} as state) = {result=Ok messages; state}
                                           
let log msg state = {state={state with messages = msg::state.messages}; result=Ok ()}

let fail state = {state; result=Failed}
                          
let if_ b m = if b then m else return ()
