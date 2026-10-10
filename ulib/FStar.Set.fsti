(*
   Copyright 2008-2014 Nikhil Swamy, Aseem Rastogi,
                       Microsoft Research, University of Maryland

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

module FStar.Set
(** Computational sets (on eqtypes): membership is a boolean function *)

(*| The type of sets of elements of an `eqtype`, with decidable membership.

    A set is a total boolean membership function, and `FStar.Set.mem` returns a
    `bool`, so membership can be tested in ordinary (non-ghost) code. Sets may
    be infinite (see `FStar.Set.complement` and `FStar.Set.intension`). The
    type is not an `eqtype`: compare sets with `FStar.Set.equal`, which is
    extensional.

    Related modules: `FStar.GSet` is the variant for elements of any type, with
    ghost boolean membership; `FStar.TSet` is the variant for elements of any
    type, with membership a `prop`. Both of those set types are erasable.
    `FStar.OrdSet` provides finite sets represented as sorted lists. *)
val set (a:eqtype)
  : Type0

(*| Extensional equality of sets: `equal s1 s2` holds when `s1` and `s2` have
    the same members.

    `FStar.Set.lemma_equal_intro` and `FStar.Set.lemma_equal_elim` (both
    triggered automatically on `equal s1 s2`) make it interchangeable with
    `==`, so asserting `equal` is the usual way to prove two sets equal:

    ```fstar
    let union_comm (s1 s2: FStar.Set.set int)
      : Lemma (FStar.Set.union s1 s2 == FStar.Set.union s2 s1)
      = assert (FStar.Set.equal (FStar.Set.union s1 s2) (FStar.Set.union s2 s1))
    ``` *)
val equal (#a:eqtype) (s1:set a) (s2:set a)
  : prop

(* destructors *)

(*| Tests whether `x` is a member of `s`; membership is decidable.

    The membership lemmas such as `FStar.Set.mem_union` describe how each
    operation affects it. *)
val mem (#a:eqtype) (x:a) (s:set a)
  : Tot bool

(* constructors *)
(*| The set with no members (see `FStar.Set.mem_empty`). *)
val empty (#a:eqtype)
  : Tot (set a)

(*| The set whose only member is `x` (see `FStar.Set.mem_singleton`). *)
val singleton (#a:eqtype) (x:a)
  : Tot (set a)

(*| The set of elements that are members of either argument (see
    `FStar.Set.mem_union`). *)
val union      : #a:eqtype -> set a -> set a -> Tot (set a)
(*| The set of elements that are members of both arguments (see
    `FStar.Set.mem_intersect`). *)
val intersect  : #a:eqtype -> set a -> set a -> Tot (set a)
(*| The set of all elements that are not members of the argument (see
    `FStar.Set.mem_complement`).

    `complement empty` is the set of all elements of the type. *)
val complement : #a:eqtype -> set a -> Tot (set a)
(*| The set whose members are the elements `x` such that `f x` is `true`.

    The result is ghost. `FStar.Set.mem_intension` states its membership; it
    has no SMT pattern and must be called explicitly. *)
val intension  : #a:eqtype -> (a -> Tot bool) -> GTot (set a)

(* Derived functions *)

(*| Two sets are disjoint when their intersection is equal to the empty set.

    `FStar.Set.disjoint_not_in_both` turns this into a statement about
    membership. *)
let disjoint (#a:eqtype) (s1: set a) (s2: set a) =
  equal (intersect s1 s2) empty

(*| `subset s1 s2` holds when every member of `s1` is a member of `s2`.

    It is a proposition, not a boolean test. *)
let subset (#a:eqtype) (s1:set a) (s2:set a) =
  forall x. mem x s1 ==> mem x s2

(*| Returns `s` with `x` added: the union of `s` and `singleton x`. *)
let add (#a:eqtype) (x:a) (s:set a) : set a =
  union s (singleton x)

(*| Returns `s` with `x` removed: the intersection of `s` and the complement of
    `singleton x`. *)
let remove (#a:eqtype) (x:a) (s:set a) : set a =
  intersect s (complement (singleton x))

(* Properties *)
(*| No element is a member of `FStar.Set.empty`.

    Triggered automatically on `mem x empty`. *)
val mem_empty: #a:eqtype -> x:a -> Lemma
   (requires True)
   (ensures (not (mem x empty)))
   [SMTPat (mem x empty)]

(*| `y` is a member of `singleton x` exactly when `x = y`.

    Triggered automatically on `mem y (singleton x)`. *)
val mem_singleton: #a:eqtype -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (singleton x) = (x=y)))
   [SMTPat (mem y (singleton x))]

(*| `x` is a member of `union s1 s2` exactly when it is a member of `s1` or
    of `s2`.

    Triggered automatically on `mem x (union s1 s2)`. *)
val mem_union: #a:eqtype -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (union s1 s2) = (mem x s1 || mem x s2)))
   [SMTPat (mem x (union s1 s2))]

(*| `x` is a member of `intersect s1 s2` exactly when it is a member of both
    `s1` and `s2`.

    Triggered automatically on `mem x (intersect s1 s2)`. *)
val mem_intersect: #a:eqtype -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (intersect s1 s2) = (mem x s1 && mem x s2)))
   [SMTPat (mem x (intersect s1 s2))]

(*| `x` is a member of `complement s` exactly when it is not a member of `s`.

    Triggered automatically on `mem x (complement s)`. *)
val mem_complement: #a:eqtype -> x:a -> s:set a -> Lemma
   (requires True)
   (ensures (mem x (complement s) = not (mem x s)))
   [SMTPat (mem x (complement s))]

(*| `x` is a member of `intension f` exactly when `f x` is `true`.

    This lemma has no SMT pattern: call it explicitly. *)
val mem_intension: #a:eqtype -> x:a -> f:(a -> Tot bool) -> Lemma
  (requires True)
  (ensures (mem x (intension f) = f x))

(*| Proves `subset s1 s2` from the fact that every member of `s1` is a member
    of `s2`.

    Triggered automatically on `subset s1 s2`. *)
val mem_subset: #a:eqtype -> s1:set a -> s2:set a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (subset s1 s2))
   [SMTPat (subset s1 s2)]

(*| From `subset s1 s2`, every member of `s1` is a member of `s2`.

    Triggered automatically on `subset s1 s2`. *)
val subset_mem: #a:eqtype -> s1:set a -> s2:set a -> Lemma
   (requires (subset s1 s2))
   (ensures (forall x. mem x s1 ==> mem x s2))
   [SMTPat (subset s1 s2)]

(* extensionality *)
(*| Two sets with the same members are `FStar.Set.equal`.

    Triggered automatically on `equal s1 s2`. *)
val lemma_equal_intro: #a:eqtype -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 = mem x s2))
    (ensures (equal s1 s2))
    [SMTPat (equal s1 s2)]

(*| Sets that are `FStar.Set.equal` are equal (`==`): extensionality for sets.

    Triggered automatically on `equal s1 s2`. *)
val lemma_equal_elim: #a:eqtype -> s1:set a -> s2:set a -> Lemma
    (requires (equal s1 s2))
    (ensures  (s1 == s2))
    [SMTPat (equal s1 s2)]

(*| Equal (`==`) sets are `FStar.Set.equal`.

    Triggered automatically on `equal s1 s2`. *)
val lemma_equal_refl: #a:eqtype -> s1:set a -> s2:set a -> Lemma
    (requires (s1 == s2))
    (ensures  (equal s1 s2))
    [SMTPat (equal s1 s2)]

(*| No element is a member of two disjoint sets.

    Triggered automatically on `disjoint s1 s2`. *)
val disjoint_not_in_both (a:eqtype) (s1:set a) (s2:set a)
  : Lemma
      (requires (disjoint s1 s2))
      (ensures (forall (x:a).{:pattern (mem x s1) \/ (mem x s2)} mem x s1 ==> ~(mem x s2)))
      [SMTPat (disjoint s1 s2)]

(* Converting lists to sets *)

(*| Returns the set of the elements of a list, by structural recursion on the
    list.

    Prefer `FStar.Set.as_set`, which normalizes this definition away. *)
let rec as_set' (#a:eqtype) (l:list a) : set a =
  match l with
  | [] -> empty
  | hd::tl -> union (singleton hd) (as_set' tl)

(*| Returns the set of the elements of a list.

    It is marked `unfold` and computes the set with `normalize_term`, so for a
    list literal the result is a plain combination of `FStar.Set.singleton`
    and `FStar.Set.union` that the SMT solver handles directly:

    ```fstar
    let _ = assert (FStar.Set.mem 2 (FStar.Set.as_set [1; 2; 3]))
    ``` *)
unfold
let as_set (#a:eqtype) (l:list a) = normalize_term (as_set' l)

(*| If `s3` is a subset of `s1` and `s1` is disjoint from `s2`, then `s3` is
    disjoint from `s2`. *)
let lemma_disjoint_subset (#a:eqtype) (s1:set a) (s2:set a) (s3:set a)
  : Lemma (requires (disjoint s1 s2 /\ subset s3 s1))
          (ensures  (disjoint s3 s2))
  = ()
