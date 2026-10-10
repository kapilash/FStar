(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Range

(*| The type of source ranges, as used by the compiler for error locations.

    A range includes a definition range and a use range, each with a file name,
    a start position and an end position (line and column). The type is
    abstract here, but it has decidable equality; construct values with
    `FStar.Range.mk_range` and inspect them with `FStar.Range.explode`. It is
    realized by the compiler's own range type, so ranges are the same type in
    user code, tactics and the compiler.

    `range` used to be sealed, which made all ranges provably equal; it no
    longer is, so ranges carry observable data. *)
val range : eqtype

(*| A dummy range, for use when no source location is available. An assumed constant. *)
val range_0 : range

(*| Builds a range from a file name, a start line and column, and an end line and column.

    An assumed primitive that reduces in the normalizer. *)
val mk_range (file: string) (from_line from_col to_line to_col: int) : Tot range
(* Retained as a primop, since the extra indirection would break the custom
error messages in QuickCode. (Guido 30/Aug/2024) *)

(*| Joins two ranges into a single range spanning both, for reporting a location that covers several terms.

    An assumed primitive that reduces in the normalizer; the interface states no
    property of the result. *)
val join_range (r1 r2 : range) : Tot range

(*| Labels a proposition with a source range and a message; logically, `labeled r msg b` is just `b`.

    Used internally by the SMT encoding to report which assertion failed. It is
    `irreducible`. *)
irreducible
let labeled (r : range) (msg: string) (b: prop) : prop = b

(*| Returns the file name, start line, start column, end line and end column of a range.

    An assumed primitive that reduces in the normalizer; no lemma relates it
    to `FStar.Range.mk_range`. *)
val explode (r : range) : Tot (string & int & int & int & int)
