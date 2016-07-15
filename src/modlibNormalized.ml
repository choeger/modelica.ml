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
   Modelica 3.x normalized library
*)

open Batteries
open Utils
open Syntax
open Flags

open ModlibInter

type constr = Array of int
            | Sort of sort
            | Var of variability
            | Cau of causality
            | Con of connectivity
            | Der of string list
                  [@@deriving eq,yojson,show]                                 

let norm_constr = function
    CArray i -> Array i
  | CSort s -> Sort s
  | CVar v -> Var v
  | CCau c -> Cau c
  | CCon c -> Con c
  | CDer d -> Der d
  | CRepl -> raise (Invalid_argument "'replaceable' is not a normalized constructor")

type class_value = Int | Real | String | Bool | Unit | ProtoExternalObject
                 | Enumeration of StrSet.t
                 | Constr of constr_value
                 | Class of object_struct
                 | Replaceable of class_value
                 | GlobalReference of Path.t
                 | DynamicReference of reference_struct
  [@@deriving eq,show,yojson,folder,mapper]

and reference_struct = {upref : int ; base : bool; downref : Name.t}

and super_class = {super_shape : super_shape ;
                   super_type : class_value;
                   super_mod : field_modification StrMap.t [@default StrMap.empty]}

and super_shape = Shape of component_kind StrMap.t
                | Primitive

and rec_term = { rec_lhs : class_path; rec_rhs : class_term }

and constr_value = { arg : class_value ; constr : constr }

and object_struct = { object_sort : sort ;
                      source_path : Path.t ;
                      public : elements_struct [@default {class_members = StrMap.empty; super = IntMap.empty; fields = StrMap.empty }];
                      protected : elements_struct [@default {class_members = StrMap.empty; super = IntMap.empty; fields = StrMap.empty }] ;
                      behavior : behavior [@default {algorithms=[]; equations=[]; initial_algorithms=[]; initial_equations=[]; external_=None}] ;
                      annotation : field_modification option [@default None] ;
                    }

and field_modification = { mod_kind : component_kind ;
                           mod_nested : field_modification StrMap.t [@default StrMap.empty] ;
                           mod_default : exp option [@default None]}

and class_field = { field_class : class_value ;
                    field_pos : int;
                    field_def : bool;
                    field_mod : field_modification [@default {mod_kind=CK_Class; mod_nested = StrMap.empty; mod_default=None}]}

and modified_class = { class_ : class_value ;
                       class_mod : field_modification StrMap.t [@default StrMap.empty]}

and elements_struct = { class_members : modified_class StrMap.t [@default StrMap.empty];
                        super : super_class IntMap.t [@default IntMap.empty];
                        fields : class_field StrMap.t [@default StrMap.empty]
                      }

(** Enhance the automatically derived mapper with map-routines for all these Map.t elements *)
let cv_mapper ?(map_behavior = fun x -> x) ?(map_expr = fun x -> x) () =
  {identity_mapper with 
   
   map_field_modification = (fun self {mod_kind; mod_nested; mod_default} ->
       let mod_nested = StrMap.map (self.map_field_modification self) mod_nested in
       let mod_default = Option.map map_expr mod_default in
       {mod_kind; mod_nested; mod_default}
     );
  
   map_object_struct = (fun self os -> {os with public = self.map_elements_struct self os.public ;
                                                protected = self.map_elements_struct self os.protected ;
                                                behavior = map_behavior os.behavior}) ;

   map_super_class = (fun self {super_shape; super_type; super_mod} ->
       let super_shape = self.map_super_shape self super_shape in
       let super_type = self.map_class_value self super_type in
       let super_mod = StrMap.map (self.map_field_modification self) super_mod in
       {super_shape; super_type; super_mod}
     );
   
   map_modified_class = (fun self {class_; class_mod} ->
       let class_ = self.map_class_value self class_ in
       let class_mod = StrMap.map (self.map_field_modification self) class_mod in
       {class_; class_mod});

   map_class_field = (fun self {field_class; field_pos; field_def; field_mod} ->
       let field_class = self.map_class_value self field_class in
       let field_mod = self.map_field_modification self field_mod in
       {field_class; field_pos; field_def; field_mod});
                      
   map_elements_struct = (fun self {class_members; super; fields} ->
       let class_members = StrMap.map (self.map_modified_class self) class_members in
       let super = IntMap.map (self.map_super_class self) super in
       let fields = StrMap.map (self.map_class_field self) fields in
       {class_members; super; fields}) ;      
}

let fields_in_order fields =
  List.fast_sort (fun (_,f1) (_,f2) -> Int.compare f2.field_pos f1.field_pos) (StrMap.bindings fields)

type flat_attributes = {
  fa_sort : sort option [@default None] ;
  fa_var : variability option [@default None];
  fa_con : connectivity option [@default None];
  fa_cau : causality option [@default None];
  fa_replaceable : bool [@default false];
}	[@@deriving show,yojson]		     

type flat_repr = {
  flat_val : class_value ;
  flat_attr : flat_attributes [@default {fa_sort=None;fa_var=None;fa_con=None;fa_cau=None;fa_replaceable=false}]
} [@@deriving show,yojson]

let no_attributes = {fa_con = None; fa_cau = None; fa_sort = None; fa_var = None; fa_replaceable = false}

let rec extract_attributes fa =
  let flat_ = extract_attributes in
  function
  | Constr {arg; constr = Var v} when fa.fa_var = None -> flat_ {fa with fa_var = Some v} arg
  | Constr {arg; constr = Con c} when fa.fa_con = None -> flat_ {fa with fa_con = Some c} arg
  | Constr {arg; constr = Cau c} when fa.fa_cau = None -> flat_ {fa with fa_cau = Some c} arg
  | Constr {arg; constr = Sort s} when fa.fa_sort = None -> flat_ {fa with fa_sort = Some s} arg
  | Constr {arg; constr} -> flat_ fa arg
  | Replaceable cv -> flat_ {fa with fa_replaceable = true} cv
  | Class os when fa.fa_sort = None -> {flat_val=Class os; flat_attr = {fa with fa_sort = Some os.object_sort}}  
  | flat_val -> {flat_val; flat_attr = fa}  

let flat = extract_attributes no_attributes

let rec unflat = function
  | {flat_val; flat_attr={fa_sort;fa_var;fa_cau;fa_con;fa_replaceable}} ->
    let unflat_sort s cv = match s with None -> cv | Some s -> begin match cv with Class os -> Class os | _ -> Constr {arg=cv; constr=Sort s} end in
    let unflat_cau c cv = match c with None -> cv | Some c -> Constr {arg=cv; constr=Cau c} in
    let unflat_con c cv = match c with None -> cv | Some c -> Constr {arg=cv; constr=Con c} in
    let unflat_var v cv = match v with None -> cv | Some v -> Constr {arg=cv; constr=Var v} in
    let unflat_repl v cv = if v then Replaceable cv else cv in
    flat_val |> (unflat_sort fa_sort) |> (unflat_var fa_var) |> (unflat_con fa_con) |> (unflat_cau fa_cau) |> (unflat_repl fa_replaceable)

let norm_cv = flat %> unflat

let no_behavior = {algorithms=[]; equations=[]; initial_algorithms=[]; initial_equations=[]; external_=None}
let empty_elements = {class_members = StrMap.empty; super = IntMap.empty; fields = StrMap.empty }
let empty_object_struct = {object_sort=Class; source_path=Path.empty; public=empty_elements; protected=empty_elements; behavior=no_behavior; annotation=None}

let empty_class = Class empty_object_struct
let no_modification = {mod_kind=CK_Class; mod_nested = StrMap.empty; mod_default=None}
let empty_modified_class = {class_ = empty_class; class_mod = StrMap.empty}
let empty_super_class = {super_type = empty_class; super_mod = StrMap.empty; super_shape=Shape StrMap.empty}

type prefix_found_struct = { found : class_path ; not_found : component list } [@@deriving show,yojson]

let show_prefix_found {found; not_found} = "No element named " ^ (show_components not_found) ^ " in " ^ (Name.show (Name.of_ptr found))

type found_struct = { found_path : class_path ;
                      found_value : class_value ;
                      found_visible : bool ;
                      found_replaceable : bool } [@@deriving show,yojson]

type search_error = [ `NothingFound | `PrefixFound of prefix_found_struct ] [@@deriving show,yojson]

type search_result = [`Found of found_struct | search_error ] [@@deriving show,yojson]

exception IllegalPath of string                         
exception CannotUpdate of string * string * string

let rec update_ (lhs:class_path) rhs ({class_members;fields;super} as elements) = match DQ.front lhs with
    None -> elements
  | Some (`SuperClass i, r) -> {elements with super = update_intmap r rhs i super} 
  | Some (`FieldType x, r) -> {elements with fields = update_field_map r rhs x fields}
  | Some (`ClassMember x, r) -> {elements with class_members = update_map r rhs x class_members}
  | Some (`Protected,_) -> raise (IllegalPath "")

and update_super_class lhs rhs ({super_type; super_shape} as cm) =
  {cm with super_type = update_class_value lhs rhs super_type;
           super_shape=update_super_shape lhs rhs super_shape;           
  }

and update_super_shape lhs rhs super_shape = match DQ.front lhs with None -> rhs.map_super_shape rhs super_shape | _ -> super_shape

and update_modified_class lhs rhs ({class_} as cm) =
  {cm with class_ = update_class_value lhs rhs class_}

and update_map lhs rhs x m =  
  StrMap.modify_def empty_modified_class x (update_modified_class lhs rhs) m

and update_field_map lhs rhs x m =  
  StrMap.modify_def {field_class=empty_class; field_pos=0; field_def=false; field_mod=no_modification}
    x (update_field_class_value lhs rhs) m

and update_field_class_value lhs rhs f = {f with field_class = update_class_value lhs rhs f.field_class}

and update_intmap lhs rhs i map =  
  IntMap.modify_def empty_super_class i (update_super_class lhs rhs) map

and update_class_value lhs rhs = function
  | Constr {constr; arg} -> Constr {constr ; arg = (update_class_value lhs rhs arg)}
  | Class ({public; protected} as os) -> begin match DQ.front lhs with
        None -> rhs.map_class_value rhs (Class (empty_object_struct))
      | Some(`Protected, q) -> Class {os with protected = update_ q rhs protected}
      | Some _ -> Class {os with public = update_ lhs rhs public}
    end
  | Replaceable cv ->
    begin match (update_class_value lhs rhs cv) with
        (Replaceable cv' | cv') -> Replaceable cv'
    end
  | (Int | Real | String | Bool | Unit | ProtoExternalObject | Enumeration _ | GlobalReference _ | DynamicReference _) as v ->
    begin match DQ.front lhs with
        None -> rhs.map_class_value rhs v
      | Some (x,xs) -> raise (CannotUpdate(Path.show_elem_t x, show_class_path xs, show_class_value v))
    end

let update lhs rhs es = update_ lhs rhs es

(** Follow Path.t pointers literally in the global class structure. This is useful for compression purposes. *)
let rec follow_path global found_path found_value path = match DQ.front path with
    None ->
    let found_replaceable = match found_value with
        Replaceable _ -> true
      | _ -> false
    in
    `Found {found_path; found_value; found_visible=true; found_replaceable}

  | Some (x,xs) -> begin
      match found_value with
      | Class os -> follow_path_os global found_path os xs x
      (* follow global references *)
      | GlobalReference g -> begin
          match DQ.front g with
            None -> raise (IllegalPath "")
          | Some (y,ys) -> begin 
              match follow_path_es global DQ.empty global ys y with
              | `Found {found_value} ->
                follow_path global found_path found_value path
              | `NothingFound | `PrefixFound _ as result -> result
            end
        end
      (* Replaceable/Constr means to look into it *)
      | Replaceable v -> begin match follow_path global found_path v path with
            `Found fs -> `Found {fs with found_replaceable=true}
          | `NothingFound | `PrefixFound _ as result -> result
        end
      | Constr {arg} -> follow_path global found_path arg path
      | _ -> `NothingFound
    end

and follow_path_os global found_path {protected; public} todo = function
    `Protected -> begin match DQ.front todo with
        None -> raise (IllegalPath "")
      | Some(x,xs) -> follow_path_es global found_path protected xs x
    end    
  | x -> follow_path_es global found_path public todo x

and follow_path_es global found_path {class_members;super;fields} todo = function
    `SuperClass n when IntMap.mem n super ->
    follow_path global (DQ.snoc found_path (`SuperClass n))
      (IntMap.find n super).super_type todo

  | `SuperClass n -> raise (IllegalPath ("super(" ^ (string_of_int n) ^ ")"))

  | `FieldType x when StrMap.mem x fields ->
    follow_path global (DQ.snoc found_path (`FieldType x))
      (StrMap.find x fields).field_class todo

  | `FieldType x -> raise (IllegalPath x)

  | `ClassMember x when StrMap.mem x class_members ->
    follow_path global (DQ.snoc found_path (`ClassMember x))
      (StrMap.find x class_members).class_ todo

  | `ClassMember x -> raise (IllegalPath x)
  | `Protected -> raise (IllegalPath "protected")

let lookup_path_direct global p = match DQ.front p with
    Some(x,xs) -> follow_path_es global DQ.empty global xs x
  | None -> raise (Failure "empty path")

exception NotFlat


let max_var a b = match (a,b) with (None,_) -> None
                                 | (_,None) -> None
                                 | (Some _, Some Discrete) -> Some Discrete
                                 | (Some Discrete, Some _) -> Some Discrete
                                 | (Some (Parameter | Constant), Some Parameter) -> Some Parameter
                                 | (Some Parameter, Some Constant) -> Some Parameter
                                 | (Some Constant, Some Constant) -> Some Constant

let ft_of_kcs kcs = match DQ.rear kcs with Some(_, {known_type}) -> known_type
                                         | None -> None

let rec tf_of_e e =
  let open Result.Monad in
  let rec variability ?limit cs = match DQ.front cs with    
      Some({kind=CK_Class | CK_Constant}, r) -> do_ ;
      variability ~limit:Constant r ;     
    | Some({kind=CK_Parameter; component}, r) ->
      begin match limit with
          Some Constant -> Bad {type_error=Printf.sprintf "Cannot access non-constant element '%s'" component.ident.txt;
                                error_src = e}
        | _ -> variability ~limit:Parameter r
      end
    | Some({kind=CK_Discrete; component}, r) ->
      begin match limit with
          Some (Parameter | Constant) -> Bad {type_error=Printf.sprintf "Cannot access non-discrete element '%s'" component.ident.txt;
                                error_src = e}
        | _ -> variability ~limit:Discrete r
      end
    | Some(_, r) -> variability ?limit r
    | None -> return limit
  in
  match e with
    ComponentReference (UnknownRef _)->
    Bad {type_error = "Unknown reference"; error_src=e}
  | ComponentReference (KnownRef {known_components=kcs} | RootRef kcs) ->
    begin match ft_of_kcs kcs with
        None ->
        Bad {type_error = "Unknown reference"; error_src=e}    
      | Some t ->
        do_ ;
        v <-- variability kcs ; 
        return (t, v)
    end
      
  | And {left; right} -> do_ ;
    (lt, lv) <-- tf_of_e left ;
    (lt', lv') <-- tf_of_e right ;
    begin match (lt, lt') with
        (FTBool, FTBool)-> return (FTBool, max_var lv lv')
      | (FTBool, _) -> Bad {error_src=right; type_error="Expected Boolean"}
      | (_, _) -> Bad {error_src=left; type_error="Expected Boolean"}
    end            
    
  | Mul {left; right} -> do_ ;
    (lt, lv) <-- tf_of_e left ;
    (lt', lv') <-- tf_of_e right ;
    begin match (lt, lt') with
        (FTInteger, FTInteger) -> return (FTInteger, max_var lv lv')
      | (FTReal, FTReal) -> return (FTReal, max_var lv lv')
      | _ -> Bad {error_src=e; type_error="Illegal Arithmetic Operands"}
    end

  | Real _ -> return (FTReal, None)
  | Int _ -> return (FTInteger, None)
  | String _ -> return (FTString, None)
  | Bool _ -> return (FTBool, None)

  | _ -> Bad {error_src=e; type_error="Type not yet implemented: " ^ (show_exp e)}

