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

(** Normalization of classLang expressions *)

open Batteries
open Utils
open Location
open Report

module Inter = ModlibInter
module Normalized = ModlibNormalized
module Lookup = ModlibLookup
module Compress = ModlibCompress
module Trans = ModlibTrans
module Deps = ModlibInterDeps
module NormSig = ModlibNormSig
open Inter
open NormSig
open Normalized

type library = { signature : Normalized.elements_struct ; implementation : Inter.value_stmt list }

let rec collect_impl_pkg impl {FileSystem.package_unit; external_units; sub_packages} =
  let pkgs_impl = List.fold_left (fun impl pkg -> collect_impl_pkg impl pkg) impl sub_packages in 
  List.fold_left (fun impl u -> u.Trans.impl_code @ impl) pkgs_impl (package_unit :: external_units)

let collect_impl {FileSystem.root_units; root_packages} =
  let pkgs_impl = List.fold_left (fun impl pkg -> collect_impl_pkg impl pkg) [] root_packages in 
  List.fold_left (fun impl u -> u.Trans.impl_code @ impl) pkgs_impl root_units

let sort_impl map stmt =
  Report.do_ ;
  scope <-- stratify_ptr stmt.lhs.scope ;
  return (
  PathMap.add scope 
  begin if PathMap.mem scope map then
    stmt :: (PathMap.find scope map)
  else
    [stmt]
  end map) 
    
let norm_pkg_root root =
  Report.do_ ;
  (* normalize signature *)
  signature <-- NormSig.norm_pkg_root root ;
  (* collect statements and sort by context *)
  implementation <-- Report.fold sort_impl PathMap.empty (collect_impl root) ;
  return {signature; implementation=[]}
  
      
