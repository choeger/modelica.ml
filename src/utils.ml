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

type position = Lexing.position = {
  pos_fname : string;
  pos_lnum : int;
  pos_bol : int;
  pos_cnum : int;
} [@@deriving yojson]

type location = Location.t = {
  loc_start: position;
  loc_end: position;
  loc_ghost: bool;
} [@@deriving yojson]

type 'a loc = 'a Location.loc = { txt : 'a; loc : location; } [@@deriving yojson]

let print_loc l = Location.print Format.str_formatter l ; Format.flush_str_formatter ()

type token =
    GT | LT | NEQ | GEQ | LEQ | EQ | EQEQ | LPAREN | RPAREN | LBRACKET | RBRACKET | LBRACE | RBRACE | SEMICOLON | COMMA | DOT | COLON | COLONEQ
  | INT of int
  | FLOAT of float
  | IDENT of string
  | QIDENT of string
  | STRING of string
  | DOTPOWER | POWER | PLUS | MINUS | TIMES | DIV | DOTPLUS | DOTMINUS | DOTTIMES | DOTDIV
  | EOF
  | ALGORITHM | DISCRETE | FALSE | LOOP | PURE | AND | EACH | FINAL | MODEL | RECORD | ANNOTATION | ELSE
  | FLOW | NOT | REDECLARE | ASSERT | ELSEIF | FOR | OPERATOR | REPLACEABLE | BLOCK | ELSEWHEN | FUNCTION | OR | RETURN
  | BREAK | ENCAPSULATED | IF | OUTER | STREAM | CLASS | END | IMPORT | OUTPUT | THEN | CONNECT | ENUMERATION | IMPURE
  | PACKAGE | TRUE | CONNECTOR | EQUATION | IN | PARAMETER | TYPE | CONSTANT | EXPANDABLE | INITIAL | PARTIAL | WHEN
  | CONSTRAINEDBY | EXTENDS | INNER | PROTECTED | WHILE | DER | EXTERNAL | INPUT | PUBLIC | WITHIN
  | ENDWHEN | ENDIF | ENDFOR | ENDWHILE | END_IDENT of string | INITIAL_EQUATION | INITIAL_ALGORITHM
    [@@deriving show]

module StdFormat = Format
open Batteries
module Format = StdFormat

exception StructuralError of string

module type RichOrderedType = sig
  type t [@@deriving show,eq,ord,yojson,sexp]
end

module RichStr = struct
  open Sexplib.Std
  type t = string[@@deriving show,eq,ord,yojson,sexp]
end

module RichInt = struct
  open Sexplib.Std
  type t = int[@@deriving show,eq,ord,yojson,sexp]
end

module RichMap(Ord : RichOrderedType) = struct
  include Map.Make(Ord)

  let union m1 m2 = Enum.fold (fun m (k,v) -> add k v m) m1 (enum m2)
  let find_or_else v x m = if mem x m then find x m else v
  let to_yojson a m = `List (List.map (fun (k,v) -> `Tuple [Ord.to_yojson k; a v]) (bindings m))                                            

  let of_yojson f js =
    let rec h mr kv =
      match (mr,kv) with
        `Ok m, (`Tuple [k;v]) -> begin
          match (Ord.of_yojson k, f v) with
            (_, (`Error _ as e)) | (`Error _ as e, _) -> e
          | (`Ok k', `Ok v') -> `Ok (add k' v' m)
        end
      | (`Ok _, _) -> `Error "expected a 2-tuple"
      | (`Error _ as e, _) -> e
    in
    match js with `List ls -> List.fold_left h (`Ok empty) ls
                | _ -> `Error "expected a json-list"                                         

  let of_list bs = of_enum (List.enum bs)
  open StdFormat 
  let pp pp_v fmt s =
    let pp_comma fmt () = fprintf fmt "," in
    let pp_pair fmt (k,v) = fprintf fmt "%a@ =@ %a" Ord.pp k pp_v v in
    fprintf fmt "@[{%a}@]" (pp_print_list ~pp_sep:pp_comma pp_pair) (bindings s)

  open Sexplib.Std
  open Sexplib.Conv
  let t_of_sexp a_of_sexp s =
    of_list (list_of_sexp (pair_of_sexp Ord.t_of_sexp a_of_sexp) s)

  let sexp_of_t sexp_of_a s =
    sexp_of_list (sexp_of_pair Ord.sexp_of_t sexp_of_a) (bindings s)
  
  let show poly_a = [%derive.show : 'a t]

  let eq poly_a = [%derive.eq : 'a t]
end

module RichSet(Ord : RichOrderedType) = struct
  include Set.Make(Ord) 

  let to_yojson s = `List (List.map (fun e -> Ord.to_yojson e) (elements s))

  let of_yojson js =
    let rec h sr v =
      match sr with
        `Ok s -> begin
          match Ord.of_yojson v with
          | `Ok v' -> `Ok (add v' s)
          | `Error _ as e -> e
        end
      | `Error _ as e -> e
    in
    match js with `List ls -> List.fold_left h (`Ok empty) ls
                | _ -> `Error "expected a json-list"                                             

  open StdFormat
  let pp fmt s = let pp_comma fmt () = fprintf fmt "," in fprintf fmt "@[{%a}@]" (pp_print_list ~pp_sep:pp_comma Ord.pp) (elements s)

  let show s = pp (Format.str_formatter) s ; Format.flush_str_formatter ()

  module Map = RichMap(Ord)
  
  let mkmap f s =
    Map.of_enum (Enum.map (fun k -> (k, f k)) (enum s))

  open Sexplib.Std
  open Sexplib.Conv
  let t_of_sexp s =
    of_list (list_of_sexp Ord.t_of_sexp s)

  let sexp_of_t s =
    sexp_of_list Ord.sexp_of_t (elements s)

end

module IntSet = RichSet(RichInt)
module StrSet = RichSet(RichStr)

module IntMap = RichMap(RichInt)
module StrMap = RichMap(RichStr)

module List = List
  
open Sexplib.Conv (* string_of_sexp *)       
module DQ = struct include BatDeque

  let compare f a b = Enum.compare f (enum a) (enum b)

  let equal f a b = Enum.equal f (enum a) (enum b)

  let singleton x = cons x empty

  open StdFormat

  let t_of_sexp f s = of_list (list_of_sexp f s)

  let sexp_of_t f dq = sexp_of_list f (to_list dq) 
  
  let pp pp_v fmt dq = let pp_comma fmt () = fprintf fmt "," in
    fprintf fmt "@[%a@]" (pp_print_list ~pp_sep:pp_comma pp_v) (to_list dq)

  let to_yojson a dq = `List (List.map a (to_list dq))

  let of_yojson f js =
    let rec h sr v =
      match sr with
        `Ok s -> begin
          match f v with
            `Error _ as e -> e
          | `Ok v' -> `Ok (snoc s v')
        end
      | `Error _ as e -> e
    in
    match js with `List ls -> List.fold_left h (`Ok empty) ls
                | _ -> `Error "expected a json-list"                                             
end

let unloc {Location.txt} = txt

let lunloc xs = List.map unloc xs

module Name = struct
  open Sexplib.Std
  type t = string DQ.t [@@deriving show,eq,ord,yojson,sexp]

  let hash = Hashtbl.hash

  let empty = DQ.empty

  let is_empty = DQ.is_empty

  let of_list = DQ.of_list

  let to_list = DQ.to_list

  let singleton = DQ.singleton

  let front = DQ.front

  let rear = DQ.rear

  let size = DQ.size
  
  let rec of_ptr_ tmp dq = match DQ.front dq with
    | None -> tmp
    | Some ((`SuperClass _  | `Protected), r) -> of_ptr_ tmp r
    | Some ((`FieldType x), r) -> of_ptr_ (DQ.snoc tmp x) r
    | Some ((`ClassMember x | `Any x), r) -> of_ptr_ (DQ.snoc tmp x) r

  let of_ptr dq = of_ptr_ DQ.empty dq
end

module NameMap = RichMap(Name)
module NameSet = RichSet(Name)
