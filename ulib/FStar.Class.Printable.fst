(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Brian G. Milnes
*)

module FStar.Class.Printable

open FStar.String
open FStar.Seq.Properties

(*| Typeclass of types whose values can be converted to a string for display.

    Field:

    - `to_string`: the conversion.

    Instances cover the primitive types, the machine integers, `list`, `option`, `either`, `FStar.Seq.Base.seq` and tuples up to 7 components. Lists print as `[x; y]`, sequences as `<x; y>`, tuples as `(x, y)` and strings with surrounding double quotes.

    Because of the generic instance for refinement types (`FStar.Class.Printable.printable_ref`), resolution can run out of fuel when the argument type still contains unresolved parts; annotating the type helps:

    ```fstar
    let _ = assert_norm (FStar.Class.Printable.to_string #(option int & bool) (Some 1, true) == "((Some 1), true)")
    ``` *)
class printable (a:Type) =
{
  to_string : a -> string
}

(* First the prim types. *)

(*| Prints `()`. *)
instance printable_unit : printable unit =
{
  to_string = (fun _ -> "()")
}

(*| Prints `true` or `false`, using `Prims.string_of_bool`. *)
instance printable_bool : printable bool =
{
  to_string = Prims.string_of_bool
}

(*| Prints a natural number in decimal, using `Prims.string_of_int`. *)
instance printable_nat : printable nat =
{
  to_string = Prims.string_of_int
}

(*| Prints an integer in decimal, using `Prims.string_of_int`. *)
instance printable_int : printable int =
{
  to_string = Prims.string_of_int
}

(* An instance for refinements, they can be printed as long
as the base type is printable. This allows to print [nat],
for instance. *)
(*| Prints a value of a refinement type `x:a{p x}` as a value of its base type `a`. *)
instance printable_ref #a #p (d : printable a) : printable (x:a{p x}) =
{
  to_string = d.to_string
}

(*| Prints a list as `[x1; x2; ...]`, printing each element with its instance. *)
instance printable_list (#a:Type) (x:printable a) : printable (list a) =
{
  to_string = (fun l -> "[" ^ FStar.String.concat "; " (List.Tot.map to_string l) ^ "]")
}

(*| Prints a string surrounded by double quotes, without escaping its contents. *)
instance printable_string : printable string =
{
  to_string = fun x -> "\"" ^ x ^ "\""
}

(*| Prints `None`, or `(Some x)` with `x` printed by its instance. *)
instance printable_option #a {| printable a |} : printable (option a) =
{
  to_string = (function None -> "None" | Some x -> "(Some " ^ to_string x ^ ")")
}

(*| Prints `(Inl x)` or `(Inr y)`, with the payload printed by its instance. *)
instance printable_either #a #b {| printable a |} {| printable b |} : printable (either a b) =
{
  to_string =
    (function Inl x -> "(Inl " ^ to_string x ^ ")" |
              Inr x -> "(Inr " ^ to_string x ^ ")")
}

(* Then the base types. *)

(*| Prints a character as a one-character string, using `FStar.String.string_of_char`. *)
instance printable_char : printable FStar.Char.char =
{
  to_string = string_of_char
}

(* Floats are not yet well implemented, so these are placeholders.*)
(*
instance printable_float : printable FStar.Float.float =
{
  to_string = FStar.Float.to_string
}

instance printable_double : printable FStar.Float.double =
{
  to_string = FStar.Float.to_string
}
*)

(*| Prints a `FStar.UInt8.byte` with `FStar.UInt8.to_string`. *)
instance printable_byte : printable FStar.UInt8.byte =
{
  to_string = FStar.UInt8.to_string
}

(*| Prints a `FStar.Int8.t` with `FStar.Int8.to_string`. *)
instance printable_int8 : printable FStar.Int8.t =
{
  to_string = FStar.Int8.to_string
}

(*| Prints a `FStar.UInt8.t` with `FStar.UInt8.to_string`. *)
instance printable_uint8 : printable FStar.UInt8.t =
{
  to_string = FStar.UInt8.to_string
}

(*| Prints a `FStar.Int16.t` with `FStar.Int16.to_string`. *)
instance printable_int16 : printable FStar.Int16.t =
{
  to_string = FStar.Int16.to_string
}

(*| Prints a `FStar.UInt16.t` with `FStar.UInt16.to_string`. *)
instance printable_uint16 : printable FStar.UInt16.t =
{
  to_string = FStar.UInt16.to_string
}

(*| Prints a `FStar.Int32.t` with `FStar.Int32.to_string`. *)
instance printable_int32 : printable FStar.Int32.t =
{
  to_string = FStar.Int32.to_string
}

(*| Prints a `FStar.UInt32.t` with `FStar.UInt32.to_string`. *)
instance printable_uint32 : printable FStar.UInt32.t =
{
  to_string = FStar.UInt32.to_string
}

(*| Prints a `FStar.Int64.t` with `FStar.Int64.to_string`. *)
instance printable_int64 : printable FStar.Int64.t =
{
  to_string = FStar.Int64.to_string
}

(*| Prints a `FStar.UInt64.t` with `FStar.UInt64.to_string`. *)
instance printable_uint64 : printable FStar.UInt64.t =
{
  to_string = FStar.UInt64.to_string
}

(* Placeholders in case someone build a 128 bit integer printer.
instance printable_int128 : printable FStar.Int128.t =
{
  to_string = FStar.Int128.to_string
}

instance printable_uint128 : printable FStar.UInt128.t =
{
  to_string = FStar.UInt128.to_string
}
*)

(* Up to 7 sized tuples, anything more and why are you using tuples? *)
(*| Prints a pair as `(x, y)`. *)
instance printable_tuple2 #a #b {| printable a |} {| printable b |} : printable (a & b) =
{
  to_string = (fun (x, y) -> "(" ^ to_string x ^ ", " ^ to_string y ^ ")")
}

(*| Prints a triple as `(x, y, z)`. *)
instance printable_tuple3
  #t0 #t1 #t2
  {| printable t0 |} {| printable t1 |} {| printable t2 |}
: printable (tuple3 t0 t1 t2) =
{
  to_string =
  (fun (v0,v1,v2) ->
    "(" ^
    to_string v0 ^ ", " ^
    to_string v1 ^ ", " ^
    to_string v2 ^ ")" )
}

(*| Prints a 4-tuple as a parenthesized, comma-separated list of its components. *)
instance printable_tuple4
  #t0 #t1 #t2 #t3
  {| printable t0 |} {| printable t1 |} {| printable t2 |} {| printable t3 |}
: printable (tuple4 t0 t1 t2 t3) =
{
  to_string =
  (fun (v0,v1,v2,v3) ->
    "(" ^
    to_string v0 ^ ", " ^
    to_string v1 ^ ", " ^
    to_string v2 ^ ", " ^
    to_string v3 ^ ")" )
}

(*| Prints a 5-tuple as a parenthesized, comma-separated list of its components. *)
instance printable_tuple5
  #t0 #t1 #t2 #t3 #t4
  {| printable t0 |} {| printable t1 |} {| printable t2 |} {| printable t3 |}
  {| printable t4 |}
: printable (tuple5 t0 t1 t2 t3 t4) =
{
  to_string =
  (fun (v0,v1,v2,v3,v4) ->
    "(" ^
    to_string v0 ^ ", " ^
    to_string v1 ^ ", " ^
    to_string v2 ^ ", " ^
    to_string v3 ^ ", " ^
    to_string v4 ^ ")" )
}

(*| Prints a 6-tuple as a parenthesized, comma-separated list of its components. *)
instance printable_tuple6
  #t0 #t1 #t2 #t3 #t4 #t5
  {| printable t0 |} {| printable t1 |} {| printable t2 |} {| printable t3 |}
  {| printable t4 |} {| printable t5 |}
: printable (tuple6 t0 t1 t2 t3 t4 t5) =
{
  to_string =
  (fun (v0,v1,v2,v3,v4,v5) ->
    "(" ^
    to_string v0 ^ ", " ^
    to_string v1 ^ ", " ^
    to_string v2 ^ ", " ^
    to_string v3 ^ ", " ^
    to_string v4 ^ ", " ^
    to_string v5 ^ ")" )
}


(*| Prints a 7-tuple as a parenthesized, comma-separated list of its components. *)
instance printable_tuple7
  #t0 #t1 #t2 #t3 #t4 #t5 #t6
  {| printable t0 |} {| printable t1 |} {| printable t2 |} {| printable t3 |}
  {| printable t4 |} {| printable t5 |} {| printable t6 |}
: printable (tuple7 t0 t1 t2 t3 t4 t5 t6) =
{
  to_string =
  (fun (v0,v1,v2,v3,v4,v5,v6) ->
    "(" ^
    to_string v0 ^ ", " ^
    to_string v1 ^ ", " ^
    to_string v2 ^ ", " ^
    to_string v3 ^ ", " ^
    to_string v4 ^ ", " ^
    to_string v5 ^ ", " ^
    to_string v6 ^ ")" )
}

(* Sequences, with a <...> syntax. *)

(*
instance printable_seq (#a:Type) (x:printable a) : printable (Seq.seq a) =
{
  to_string =
    (fun l -> "<" ^
           FStar.String.concat "; " (List.Tot.map to_string (Seq.seq_to_list l)) ^
           ">")
}

*)


(*| Prints a sequence as `<x1; x2; ...>`, printing each element with its instance. *)
instance printable_seq (#b:Type) (x:printable b) : printable (Seq.seq b) =
{
  to_string =
    (fun s -> 
     let strings_of_b = map_seq to_string s
     in
     "<" ^
       FStar.String.concat "; " (Seq.seq_to_list strings_of_b) 
     ^ ">")
}
