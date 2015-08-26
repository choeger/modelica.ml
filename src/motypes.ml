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


(**
 Modelica 3.x normalized types
 *)
module StdFormat = Format
open Batteries
module Format = StdFormat
open Utils
open Ast.Flags
module DS = Syntax

module Name = struct         
  type t = string DQ.t [@@deriving show, yojson]
                                                                                        
  let str_compare a b = String.compare a b 

  let compare a b = Enum.compare str_compare (DQ.enum a) (DQ.enum b)
                                 
  let hash = Hashtbl.hash
               
  let equal a b = compare a b = 0
                                  
  let empty = DQ.empty

  let is_empty = DQ.is_empty
                
  let of_list = DQ.of_list

  let to_list = DQ.to_list
		  
  let singleton = DQ.singleton
                  
  let rec scope_of_ptr_ tmp dq = match DQ.front dq with
    | None -> tmp
    | Some ((`FieldType _ | `Any _ | `SuperClass _ ), _) -> tmp
    | Some (`Protected, r) -> scope_of_ptr_ tmp r
    | Some ((`ClassMember x), r) -> scope_of_ptr_ (DQ.snoc tmp x) r

  let scope_of_ptr dq = match (DQ.rear dq) with
      Some(xs,`ClassMember x) -> (scope_of_ptr_ DQ.empty xs)
    | _ -> (scope_of_ptr_ DQ.empty dq)
                  
  let rec of_ptr_ tmp dq = match DQ.front dq with
    | None -> tmp
    | Some ((`SuperClass _  | `Protected), r) -> of_ptr_ tmp r
    | Some ((`FieldType x), r) -> of_ptr_ (DQ.snoc tmp ("type_of_" ^ x)) r
    | Some ((`ClassMember x | `Any x), r) -> of_ptr_ (DQ.snoc tmp x) r
								
  let of_ptr dq = of_ptr_ DQ.empty dq
                                                                        
end

module NameMap = Map.Make(Name)
module NameSet = Set.Make(Name)
                         
type constr =  CArray of int
             | CSort of sort
             | CRepl
             | CVar of variability
             | CCau of causality
             | CCon of connectivity
             | CDer of string list
                         [@@deriving yojson,eq,show]

type class_path_elem = [`Protected | `ClassMember of string | `FieldType of string | `SuperClass of int] [@@deriving eq,show,yojson]

type class_path = class_path_elem DQ.t [@@deriving eq,show,yojson]
                                                                                                     
type class_ptr_elem = [class_path_elem | `Any of string] [@@deriving eq,show,yojson]
						 
type class_ptr = class_ptr_elem DQ.t [@@deriving eq,show,yojson]

type class_term = Reference of DS.name
                | RedeclareExtends
                | Empty of open_class
                | Close
                | RootReference of DS.name
		| KnownPtr of class_ptr
                | PInt | PReal | PString | PBool | PExternalObject
                | PEnumeration of StrSet.t
                | Constr of class_constr
                | Delay of class_term
                    [@@deriving yojson,eq,show]

and open_class = { class_sort : sort ; class_name : Name.t }
                    
and  class_constr = { constr : constr ; arg : class_term }
                      
type class_stmt = {lhs : class_ptr ; rhs : class_term} [@@deriving eq,show,yojson]
                                                       
type class_program = class_stmt list [@@deriving show,yojson]
      
module Normalized = struct
    
    type constr =  Array of int
                 | Sort of sort
                 | Var of variability
                 | Cau of causality
                 | Con of connectivity
                 | Der of string list
                                 [@@deriving yojson,show,eq]                                 
				 
    let norm_constr = function
        CArray i -> Array i
      | CSort s -> Sort s
      | CVar v -> Var v
      | CCau c -> Cau c
      | CCon c -> Con c
      | CDer d -> Der d
      | CRepl -> raise (Invalid_argument "'replaceable' is not a normlized constructor")
                       
    type class_value = Int | Real | String | Bool | Unit | ProtoExternalObject
                       | Enumeration of StrSet.t
                       | Constr of constr_value
                       | Class of object_struct
                       | Replaceable of class_value
                       | GlobalReference of Name.t
                       | Recursive of rec_term
		       | DynamicReference of Name.t
                                               [@@deriving eq,show,yojson]

     and rec_term = { rec_lhs : class_path; rec_rhs : class_term }
                                        
     and constr_value = { arg : class_value ; constr : constr }
                                 
     and object_struct = { object_sort : sort ;
                           source_name : Name.t;
                           public : elements_struct [@default {class_members = StrMap.empty; super = IntMap.empty; fields = StrMap.empty }];
                           protected : elements_struct [@default {class_members = StrMap.empty; super = IntMap.empty; fields = StrMap.empty }] ;
			 }
                                                                 
     and elements_struct = { class_members : class_value StrMap.t [@default StrMap.empty];
                             super : class_value IntMap.t [@default IntMap.empty];
                             fields : class_value StrMap.t [@default StrMap.empty]
			   }
                             
    type flat_attributes = {
	fa_sort : sort option [@default None] ;
	fa_var : variability option [@default None];
	fa_con : connectivity option [@default None];
	fa_cau : causality option [@default None];
      }	[@@deriving eq,show,yojson]		     

    type flat_repr = {
	flat_val : class_value ;
	flat_attr : flat_attributes [@default {fa_sort=None;fa_var=None;fa_con=None;fa_cau=None}]
      } [@@deriving eq,show,yojson]
	
    let rec flat_ fa = function
      | Constr {arg; constr = Var v} when fa.fa_var = None -> flat_ {fa with fa_var = Some v} arg
      | Constr {arg; constr = Con c} when fa.fa_con = None -> flat_ {fa with fa_con = Some c} arg
      | Constr {arg; constr = Cau c} when fa.fa_cau = None -> flat_ {fa with fa_cau = Some c} arg
      | Constr {arg; constr = Sort s} when fa.fa_sort = None -> flat_ {fa with fa_sort = Some s} arg
      | Constr {arg; constr} -> flat_ fa arg
      | Replaceable cv -> begin match flat_ fa cv with
				  {flat_val = Replaceable cv ; flat_attr } as fv -> fv
				| fv -> {fv with flat_val = Replaceable fv.flat_val}
			  end
      | flat_val -> {flat_val; flat_attr = fa}  

    let flat = flat_ {fa_con = None; fa_cau = None; fa_sort = None; fa_var = None}
		     
    let rec unflat = function
      | {flat_val = Replaceable flat_val} as fv -> Replaceable (unflat {fv with flat_val})
      | {flat_val; flat_attr={fa_sort;fa_var;fa_cau;fa_con}} ->
	 let unflat_sort s cv = match s with None -> cv | Some s -> Constr {arg=cv; constr=Sort s} in
	 let unflat_cau c cv = match c with None -> cv | Some c -> Constr {arg=cv; constr=Cau c} in
	 let unflat_con c cv = match c with None -> cv | Some c -> Constr {arg=cv; constr=Con c} in
	 let unflat_var v cv = match v with None -> cv | Some v -> Constr {arg=cv; constr=Var v} in
	 flat_val |> (unflat_sort fa_sort) |> (unflat_var fa_var) |> (unflat_con fa_con) |> (unflat_cau fa_cau)

    let norm_cv = flat %> unflat											   												   
    let empty_elements = {class_members = StrMap.empty; super = IntMap.empty; fields = StrMap.empty }
    let empty_object_struct = {object_sort=Class; source_name=Name.singleton "EMPTY"; public=empty_elements; protected=empty_elements}

    let empty_class = Class empty_object_struct 

    let rec compress = function
        Class os ->
	Class {os with public = compress_elements os.public; protected = compress_elements os.protected }
      | Constr {constr; arg} -> Constr {constr; arg = compress arg}
      | Replaceable v -> Replaceable (compress v)
      | v -> v
               
    and compress_elements es = {es with fields = StrMap.map pack_class es.fields; super = IntMap.map pack_class es.super;
					class_members = StrMap.map compress es.class_members }

    and pack_class = function
        Class os -> GlobalReference os.source_name
      | Constr {constr; arg} -> Constr {constr; arg = pack_class arg}
      | Replaceable v -> Replaceable (pack_class v)
      | v -> v

    type type_environment = { classes : class_value StrMap.t ;
                              values : class_value StrMap.t } [@@deriving show]

    let empty_env = { classes = StrMap.empty; values = StrMap.empty }

    let env_merge a b = {classes = StrMap.union a.classes b.classes; values = StrMap.union a.values b.values}
                      
    type environment = {outside : type_environment ;
                        inside : type_environment } [@@deriving show]
               
    let rec elements_env inside {class_members; super; fields} =
      let inside = IntMap.fold (fun k v e -> inherit_env e v) super inside in
      let add_class k v c = {c with classes = StrMap.add k v c.classes} in
      let add_field k v c = {c with values = StrMap.add k v c.values} in
      let env' = StrMap.fold add_class class_members inside in
      StrMap.fold add_field fields env'

    and inherit_env env = function
        Class os -> elements_env (elements_env empty_env os.public) os.protected
      | _ -> empty_env
        
    and lexical_env outside xs v =
      let inside = inherit_env empty_env v in
      match DQ.front xs with
        Some(y,ys) -> lexical_env (env_merge inside outside) ys (StrMap.find y inside.classes)
      | None -> {inside; outside}
                                
  end
                                                                                           

                                                                                   

