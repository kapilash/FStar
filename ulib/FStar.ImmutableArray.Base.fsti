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
module FStar.ImmutableArray.Base

(*| Primitive type of immutable arrays with elements of type `a`: a sequence-like type intended to support constant-time random access, unlike `FStar.Seq.Base.seq`.

    Assumed. Values are built with `FStar.ImmutableArray.Base.of_list` and read with `FStar.ImmutableArray.Base.length` and `FStar.ImmutableArray.Base.index`. The F\* normalizer and NBE engine reduce these three functions on concrete arrays, and the module notes say the type is implemented by an OCaml array. The parameter is strictly positive, so `t` can be used in inductive type definitions. Include `FStar.ImmutableArray` for the lemmas relating arrays to lists. *)
new
val t ([@@@strictly_positive] a:Type u#a) : Type u#a

(*| An array type supports decidable equality when its element type does.

    Triggered automatically on `hasEq (t a)`. *)
val array_has_eq (a : Type) : Lemma
  (requires hasEq a)
  (ensures hasEq (t a))
  [SMTPat (hasEq (t a))]

(*| Creates an immutable array with the elements of a list, in order.

    Assumed; specified by `FStar.ImmutableArray.to_list_of_list`. The normalizer reduces `of_list`, `length` and `index` on concrete arrays, so `assert_norm` can evaluate them:

    ```fstar
    let _ = assert_norm (FStar.ImmutableArray.length (FStar.ImmutableArray.of_list [10; 20; 30]) == 3)

    let _ = assert_norm (FStar.ImmutableArray.index (FStar.ImmutableArray.of_list [10; 20; 30]) 1 == 20)
    ``` *)
val of_list (#a:Type u#a) (l:list a) : Tot (t a)

(*| Returns the number of elements of an immutable array, which is the length of the list it was created from.

    Assumed; specified by `FStar.ImmutableArray.length_spec`. *)
val length (#a:Type) (s:t a) : Tot nat

(*| Returns the element at position `i`, which must be less than `length s`.

    Assumed; specified by `FStar.ImmutableArray.index_spec`. The bound is a refinement, so an out-of-bounds access does not typecheck. *)
val index (#a:Type) (s:t a) (i:nat { i < length s }) : Tot a
