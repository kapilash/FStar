(*
   Copyright 2008-2025 Microsoft Research

   Authors: Guido Martínez

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

module FStar.RBSet

(* This module implements sets based on red-black trees.
   It does not expose functional properties, it is mostly
   useful for unverified code. *)

open FStar.Class.Ord.Raw

(*| Abstract type of finite sets of elements of type `a`, implemented as red-black trees.

    Elements are compared with an `FStar.Class.Ord.Raw.ord` instance, which
    most operations take as a typeclass argument; two elements are the same
    when the comparison says they are equal. All operations are total, but the
    interface states no functional specification, so the behaviour described
    in these docs is that of the implementation and cannot be used in proofs.
    The module is mostly useful for unverified code. Use `FStar.RBSet.equal`
    to compare sets.

    ```fstar
    let small_set : FStar.RBSet.t int = FStar.RBSet.from_list [3; 1; 2]
    let has_two : bool = FStar.RBSet.mem 2 small_set
    ``` *)
new val t (a:Type0) : Type0

(*| The empty set. *)
val empty () : t 'a

(*| The set containing only `x`. *)
val singleton (x : 'a) : t 'a

(*| Tests whether a set has no elements. *)
val is_empty (s : t 'a) : bool

(*| Adds an element to a set; returns the set unchanged if an equal element is already present. *)
val add {| ord 'a |} (x:'a) (s : t 'a) : t 'a

(*| Keeps only the elements for which `predicate` is `true`. *)
val filter {| ord 'a |} (predicate : 'a -> bool) (set : t 'a): t 'a

(*| Removes the smallest element of a nonempty set, returning the remaining set and that element.

    Requires `not (is_empty s)`. The result is the pair of the remaining set
    and the element, in that order. *)
val extract_min #a {| ord a |} (s : t a{not (is_empty s)}) : t a & a

(*| Removes an element from a set; returns the set unchanged if it is not present. *)
val remove {| ord 'a |} (x : 'a) (s : t 'a) : t 'a

(*| Tests whether an element belongs to a set. *)
val mem {| ord 'a |} (x : 'a) (s : t 'a) : bool

(*| The elements of a set, in increasing order. *)
val elems (s : t 'a) : list 'a

(*| Tests whether two sets have the same elements.

    Compares `FStar.RBSet.elems s1` and `FStar.RBSet.elems s2` with the
    equality of the `ord` instance. *)
val equal {| ord 'a |} (s1 s2 : t 'a) : bool

(*| The union of two sets. *)
val union {| ord 'a |} (s1 s2 : t 'a) : t 'a

(*| The intersection of two sets: the elements of `s1` that are also in `s2`. *)
val inter {| ord 'a |} (s1 s2 : t 'a) : t 'a

(*| The difference of two sets: the elements of `s1` that are not in `s2`. *)
val diff {| ord 'a |} (s1 s2 : t 'a) : t 'a

(*| Tests whether every element of `s1` belongs to `s2`. *)
val subset {| ord 'a |} (s1 s2 : t 'a) : bool

(*| Tests whether every element satisfies `p`; `true` for the empty set. *)
val for_all (p:'a -> bool) (s:t 'a) : bool

(*| Tests whether some element satisfies `p`; `false` for the empty set. *)
val for_any (p:'a -> bool) (s:t 'a) : bool

(*| Builds a set from the elements of a list; duplicates are kept once. *)
val from_list {| ord 'a |} (xs : list 'a) : t 'a

(*| Adds every element of a list to a set. *)
val addn {| ord 'a |} (xs : list 'a) (s : t 'a) : t 'a

(*| The union of the sets `f e` for all elements `e` of the list `l`.

    Returns the empty set for an empty list. *)
val collect #a {| ord a |} (f : a -> t a) (l : list a) : t a
