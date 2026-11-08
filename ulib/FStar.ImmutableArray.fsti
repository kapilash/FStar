(*
   Copyright 2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: N. Swamy
*)

(* This module provides a primitive type of immutable arrays,
   implemented in OCaml by an array.

   The main intended usage of this module, as suggested by Jay Lorch,
   is to provide a sequence-like type with constant-time random access
   of elements, as opposed to FStar.Seq and related types, which
   provide only linear time access.
   
   Both the F* normalizer and NBE engine are aware of this type and
   reduce its three functions, `of_list`, `length`, and `index`, by
   invoking the corresponding operations on the underlying OCaml array
   that represents a `t`.

   See tests/micro-benchmarks/TestImmutableArray.fst for some samples
   
   And also FStar.ImmutableArray, which includes this interface and 
   augments it with various properties of the functions below.
  
*)
module FStar.ImmutableArray
include FStar.ImmutableArray.Base

(*| Converts an immutable array to the list of its elements, in order; the inverse of `FStar.ImmutableArray.Base.of_list`.

    Assumed. *)
val to_list (#a:Type u#a) (s:t a)
  : Tot (list a)

(*| `to_list (of_list l) == l`.

    Triggered automatically on `of_list l`. *)
val to_list_of_list (#a:Type u#a) (l:list a)
  : Lemma (to_list (of_list l) == l)
          [SMTPat (of_list l)]

(*| `of_list (to_list s) == s`: an immutable array is determined by its list of elements. *)
val of_list_to_list (#a:Type u#a) (s:t a)
  : Lemma (of_list (to_list s) == s)

(*| The length of an immutable array is the length of its list of elements.

    Triggered automatically on `length s`. *)
val length_spec (#a:Type u#a) (s:t a)
  : Lemma (length s == FStar.List.Tot.length (to_list s))
          [SMTPat (length s)]

(*| The element at position `i` of an immutable array is element `i` of its list of elements (`FStar.List.Tot.Base.index`).

    Triggered automatically on `index s i`. *)
val index_spec (#a:Type u#a) (s:t a) (i:nat{ i < length s })
  : Lemma (index s i == FStar.List.Tot.index (to_list s) i)
          [SMTPat (index s i)]

(*| The list of elements of an array precedes the array (`<<`), so recursion from an array to its list terminates. *)
val to_list_precedes (#a:Type u#a) (s:t a)
  : Lemma (to_list s << s)

(*| A list precedes (`<<`) the array created from it. *)
let of_list_precedes (#a:Type u#a) (l:list a)
  : Lemma (l << of_list l)
  = to_list_precedes (of_list l)

(*| Every element of an immutable array precedes the array (`<<`); useful for termination of recursion over arrays of a recursive type. *)
let elem_precedes (#a:Type u#a) (s:t a) (i : nat{i < length s})
  : Lemma (index s i << s)
  = FStar.List.Tot.(
      to_list_precedes s;
      let l = to_list s in
      assert (memP (index l i) l);
      memP_precedes (index l i) l
    )

(*| Returns an immutable array with the element at zero-based index `i` replaced by `v`, leaving all other elements unchanged.

    Total. The caller must prove `i < length s`; the original array retains its elements. See `FStar.ImmutableArray.length_upd` and `FStar.ImmutableArray.index_upd` for the length and indexing properties. Extracted code may reuse storage when the array is uniquely owned, but the interface does not specify allocation or timing behaviour. *)
val upd (#a:Type u#a) (s:t a) (i:nat{ i < length s }) (v:a)
  : Tot (t a)

(*| Replacing an element with `FStar.ImmutableArray.upd` preserves the array's length.

    Requires `i < length s`. Triggered automatically on `length (upd s i v)`; useful for establishing index bounds on the updated array. *)
val length_upd (#a:Type u#a) (s:t a) (i:nat{ i < length s }) (v:a)
  : Lemma (length (upd s i v) == length s)
          [SMTPat (length (upd s i v))]

(*| Indexing an array updated at `i` returns `v` when `j = i`, and the original element at `j` otherwise.

    Both indices must be less than `length s`. Triggered automatically on `index (upd s i v) j`; `FStar.ImmutableArray.length_upd` supplies the bound for indexing the updated array. *)
val index_upd (#a:Type u#a) (s:t a) (i:nat{ i < length s }) (v:a)
              (j:nat{ j < length s })
  : Lemma (index (upd s i v) j == (if i = j then v else index s j))
          [SMTPat (index (upd s i v) j)]

(*| Returns an immutable array with `v` appended after all the elements of `s`, in their original order.

    Total, including for an empty array; the original array retains its elements. Use `FStar.ImmutableArray.to_list_push` with `FStar.ImmutableArray.length_spec` or `FStar.ImmutableArray.index_spec` to reason about the result. Extracted code may reuse storage when the array is uniquely owned, but the interface does not specify allocation or timing behaviour. *)
val push (#a:Type u#a) (s:t a) (v:a)
  : Tot (t a)

(*| The list of elements after `FStar.ImmutableArray.push s v` is `to_list s` followed by the singleton list `[v]`.

    Triggered automatically on `to_list (push s v)`. This characterizes the appended array through its list of elements. *)
val to_list_push (#a:Type u#a) (s:t a) (v:a)
  : Lemma (to_list (push s v) == FStar.List.Tot.append (to_list s) [v])
          [SMTPat (to_list (push s v))]
