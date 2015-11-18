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

(** Normalize a modelica Library's implementation part *)
open Batteries
open Utils
open Syntax
open ModlibNormalized
    
type environment_entry = EnvClass of class_value
                       | EnvField of class_value
                       | EnvVar
                         [@@deriving show]

type environment = { public_env : environment_entry StrMap.t ;
                     protected_env : environment_entry StrMap.t }
  [@@deriving show]
  
let empty_env = {public_env = StrMap.empty ; protected_env = StrMap.empty}
  
(** Environment of a class *)
let env_folder lib = { ModlibNormalized.identity_folder with
                       fold_object_struct =
                         (fun self {public; protected} env ->
                            (* Collect environments of the protected parts and combine to new protected env *)
                            let prot = self.fold_elements_struct self protected empty_env in
                            self.fold_elements_struct self public
                              {env with protected_env = StrMap.union prot.public_env (StrMap.union env.protected_env prot.protected_env)}) ;

                       fold_elements_struct =
                         (fun self {class_members;fields;super} env ->
                            let env' = IntMap.fold (fun _ -> self.fold_class_value self) super env in
                            (* Put parts into public environment by default (see above for the part sorting it out) *)
                            {env' with public_env =
                                         StrMap.union (StrMap.union env'.public_env (StrMap.map (fun v -> EnvClass v) class_members))
                                           (StrMap.map (fun v -> EnvField v.field_class) fields)}
                         )
                     }

let env lib cv =
  let f = env_folder lib in
  f.fold_class_value f cv empty_env 

let lookup_mapper env = Syntax.identity_mapper

