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
module FStar.GSet
(** Ghost sets (on Types): membership is a ghost boolean function *)

(*| The type of sets of elements of any type, with ghost boolean membership.

    `FStar.GSet.mem` returns a ghost `bool` (`GTot bool`): membership is
    decided in specifications and proofs, but cannot be tested in executable
    code, and the type is erasable. Elements need not have decidable equality.
    Sets may be infinite. Compare sets with `FStar.GSet.equal`, which is
    extensional.

    Related modules: `FStar.Set` is the variant for an `eqtype`, with total
    (non-ghost) boolean membership; `FStar.TSet` is the variant whose
    membership is a `prop`. `FStar.GSet.of_set` converts from `FStar.Set.set`. *)
[@@erasable]
val set (a: Type u#a) : Type u#a

(*| Extensional equality of sets: `equal s1 s2` holds when `s1` and `s2` have
    the same members.

    `FStar.GSet.lemma_equal_intro` and `FStar.GSet.lemma_equal_elim` (both
    triggered automatically on `equal s1 s2`) make it interchangeable with
    `==`. *)
val equal (#a:Type) (s1:set a) (s2:set a) : prop

(* destructors *)

(*| Tests, in ghost code, whether `x` is a member of `s`.

    The membership lemmas such as `FStar.GSet.mem_union` describe how each
    operation affects it. *)
val mem : #a:Type -> a -> set a -> GTot bool

(* constructors *)
(*| The set with no members (see `FStar.GSet.mem_empty`). *)
val empty      : #a:Type -> Tot (set a)
(*| The set whose only member is the argument (see `FStar.GSet.mem_singleton`). *)
val singleton  : #a:Type -> a -> Tot (set a)
(*| The set of elements that are members of either argument (see
    `FStar.GSet.mem_union`). *)
val union      : #a:Type -> set a -> set a -> Tot (set a)
(*| The set of elements that are members of both arguments (see
    `FStar.GSet.mem_intersect`). *)
val intersect  : #a:Type -> set a -> set a -> Tot (set a)
(*| The set of all elements that are not members of the argument (see
    `FStar.GSet.mem_complement`). *)
val complement : #a:Type -> set a -> Tot (set a)
(*| The set whose members are the elements `x` such that the ghost function
    `f` returns `true` on `x` (see `FStar.GSet.comprehend_mem`). *)
val comprehend (#a: Type) (f: (a -> GTot bool)) : set a
(*| Converts a `FStar.Set.set` into a `FStar.GSet.set` with the same members
    (see `FStar.GSet.mem_of_set`). *)
val of_set (#a: eqtype) (f: Set.set a) : set a

(* a property about sets *)
(*| Two sets are disjoint when their intersection is equal to the empty set.

    `FStar.GSet.disjoint_not_in_both` turns this into a statement about
    membership. *)
let disjoint (#a:Type) (s1: set a) (s2: set a) =
  equal (intersect s1 s2) empty

(* ops *)
(*| `subset s1 s2` holds when every member of `s1` is a member of `s2`. *)
type subset (#a:Type) (s1:set a) (s2:set a) :prop = forall x. mem x s1 ==> mem x s2

(* Properties *)
(*| No element is a member of `FStar.GSet.empty`.

    Triggered automatically on `mem x empty`. *)
val mem_empty: #a:Type -> x:a -> Lemma
   (requires True)
   (ensures (not (mem x empty)))
   [SMTPat (mem x empty)]

(*| `y` is a member of `singleton x` exactly when `x == y`.

    Triggered automatically on `mem y (singleton x)`. *)
val mem_singleton: #a:Type -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (singleton x) <==> (x==y)))
   [SMTPat (mem y (singleton x))]

(*| `x` is a member of `union s1 s2` exactly when it is a member of `s1` or
    of `s2`.

    Triggered automatically on `mem x (union s1 s2)`. *)
val mem_union: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (union s1 s2) = (mem x s1 || mem x s2)))
   [SMTPat (mem x (union s1 s2))]

(*| `x` is a member of `intersect s1 s2` exactly when it is a member of both
    `s1` and `s2`.

    Triggered automatically on `mem x (intersect s1 s2)`. *)
val mem_intersect: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (intersect s1 s2) = (mem x s1 && mem x s2)))
   [SMTPat (mem x (intersect s1 s2))]

(*| `x` is a member of `complement s` exactly when it is not a member of `s`.

    Triggered automatically on `mem x (complement s)`. *)
val mem_complement: #a:Type -> x:a -> s:set a -> Lemma
   (requires True)
   (ensures (mem x (complement s) = not (mem x s)))
   [SMTPat (mem x (complement s))]

(*| Proves `subset s1 s2` from the fact that every member of `s1` is a member
    of `s2`.

    Triggered automatically on `subset s1 s2`. *)
val mem_subset: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (subset s1 s2))
   [SMTPat (subset s1 s2)]

(*| From `subset s1 s2`, every member of `s1` is a member of `s2`.

    Triggered automatically on `subset s1 s2`. *)
val subset_mem: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (subset s1 s2))
   (ensures (forall x. mem x s1 ==> mem x s2))
   [SMTPat (subset s1 s2)]

(*| `x` is a member of `comprehend f` exactly when `f x` is `true`.

    Triggered automatically on `mem x (comprehend f)`. *)
val comprehend_mem (#a: Type) (f: (a -> GTot bool)) (x: a) 
  : Lemma (ensures (mem x (comprehend f) == f x))
          [SMTPat (mem x (comprehend f))]

(*| An element is a member of `of_set f` exactly when it is a member of the
    `FStar.Set.set` `f`.

    Triggered automatically on `mem x (of_set f)`. *)
val mem_of_set (#a: eqtype) (f: Set.set a) (x: a) 
  : Lemma (ensures (mem x (of_set f) <==> Set.mem x f))
          [SMTPat (mem x (of_set f))]

(* extensionality *)

(*| Two sets with the same members are `FStar.GSet.equal`.

    Triggered automatically on `equal s1 s2`. *)
val lemma_equal_intro: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 = mem x s2))
    (ensures (equal s1 s2))
    [SMTPat (equal s1 s2)]

(*| Sets that are `FStar.GSet.equal` are equal (`==`): extensionality for sets.

    Triggered automatically on `equal s1 s2`. *)
val lemma_equal_elim: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (equal s1 s2))
    (ensures  (s1 == s2))
    [SMTPat (equal s1 s2)]

(*| Equal (`==`) sets are `FStar.GSet.equal`.

    Triggered automatically on `equal s1 s2`. *)
val lemma_equal_refl: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (s1 == s2))
    (ensures  (equal s1 s2))
    [SMTPat (equal s1 s2)]

(*| No element is a member of two disjoint sets.

    Triggered automatically on `disjoint s1 s2`. *)
let disjoint_not_in_both (a:Type) (s1:set a) (s2:set a) :
  Lemma
    (requires (disjoint s1 s2))
    (ensures (forall (x:a).{:pattern (mem x s1) \/ (mem x s2)} mem x s1 ==> ~(mem x s2)))
  [SMTPat (disjoint s1 s2)]
= let f (x:a) : Lemma (~(mem x (intersect s1 s2))) = () in
  FStar.Classical.forall_intro f

(* Converting lists to sets *)

(*| Returns the set of the elements of a list, by structural recursion on the
    list. *)
let rec as_set' (#a:Type) (l:list a) : set a = 
  match l with
  | [] -> empty
  | hd::tl -> union (singleton hd) (as_set' tl)

(*| If `s3` is a subset of `s1` and `s1` is disjoint from `s2`, then `s3` is
    disjoint from `s2`. *)
let lemma_disjoint_subset (#a:Type) (s1:set a) (s2:set a) (s3:set a)
  : Lemma (requires (disjoint s1 s2 /\ subset s3 s1))
          (ensures  (disjoint s3 s2))
  = ()
