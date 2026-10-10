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
module FStar.GhostSet
(* Ghost computational sets: membership is a ghost boolean function *)

(*| Sets with ghost membership: a `set a` is a ghost boolean predicate on `a`.

    Unlike `FStar.Set.set`, the element type need not have decidable
    equality, and membership `FStar.GhostSet.mem` is ghost (`GTot bool`). The
    type is `erasable`. Equality is extensional, see
    `FStar.GhostSet.lemma_equal_elim`.

    ```fstar
    let ghost_set_example (x y: int) =
      let open FStar.GhostSet in
      let s = union (singleton x) (singleton y) in
      assert (mem x s /\ mem y s);
      assert (subset (singleton x) s)
    ``` *)
[@@erasable]
val set (a: Type u#a) : Type u#a

(*| Extensional equality of sets: `s1` and `s2` have the same members.

    Equal sets are provably equal (`==`), see
    `FStar.GhostSet.lemma_equal_elim`. *)
val equal (#a:Type) (s1:set a) (s2:set a) : prop

(* destructors *)

(*| Set membership; a ghost boolean. *)
val mem : #a:Type -> a -> set a -> GTot bool

(* constructors *)
(*| The empty set.

    Membership is characterised by `FStar.GhostSet.mem_empty`. *)
val empty      : #a:Type -> Tot (set a)
(*| The set containing exactly `x`.

    Membership is characterised by `FStar.GhostSet.mem_singleton`. *)
val singleton  : #a:Type -> a -> Tot (set a)
(*| The union of two sets.

    Membership is characterised by `FStar.GhostSet.mem_union`. *)
val union      : #a:Type -> set a -> set a -> Tot (set a)
(*| The intersection of two sets.

    Membership is characterised by `FStar.GhostSet.mem_intersect`. *)
val intersect  : #a:Type -> set a -> set a -> Tot (set a)
(*| The complement of a set: the elements of `a` not in it.

    Membership is characterised by `FStar.GhostSet.mem_complement`. *)
val complement : #a:Type -> set a -> Tot (set a)
(*| The set of elements satisfying a ghost boolean predicate `f`.

    Membership is characterised by `FStar.GhostSet.comprehend_mem`. *)
val comprehend (#a: Type) (f: (a -> GTot bool)) : set a
(*| Converts a `FStar.Set.set` to a ghost set with the same members.

    Membership is characterised by `FStar.GhostSet.mem_of_set`. *)
val of_set (#a: eqtype) (f: Set.set a) : set a

(* a property about sets *)
(*| Holds when two sets have no common member, stated as their intersection
    being equal to `FStar.GhostSet.empty`.

    See `FStar.GhostSet.disjoint_not_in_both`. *)
let disjoint (#a:Type) (s1: set a) (s2: set a) =
  equal (intersect s1 s2) empty

(* ops *)
(*| Holds when every member of `s1` is a member of `s2`.

    Introduced and eliminated automatically by `FStar.GhostSet.mem_subset`
    and `FStar.GhostSet.subset_mem`. *)
type subset (#a:Type) (s1:set a) (s2:set a) :prop = forall x. mem x s1 ==> mem x s2

(* Properties *)
(*| No element is a member of `FStar.GhostSet.empty`.

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

(*| Introduces `subset s1 s2` from the fact that every member of `s1` is a
    member of `s2`.

    Triggered automatically on `subset s1 s2`. *)
val mem_subset: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (subset s1 s2))
   [SMTPat (subset s1 s2)]

(*| Eliminates `subset s1 s2`: every member of `s1` is a member of `s2`.

    Triggered automatically on `subset s1 s2`. *)
val subset_mem: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (subset s1 s2))
   (ensures (forall x. mem x s1 ==> mem x s2))
   [SMTPat (subset s1 s2)]

(*| `x` is a member of `comprehend f` exactly when `f x` is true.

    Triggered automatically on `mem x (comprehend f)`. *)
val comprehend_mem (#a: Type) (f: (a -> GTot bool)) (x: a) 
  : Lemma (ensures (mem x (comprehend f) == f x))
          [SMTPat (mem x (comprehend f))]

(*| `x` is a member of `of_set f` exactly when it is a member of the
    `FStar.Set.set` `f`.

    Triggered automatically on `mem x (of_set f)`. *)
val mem_of_set (#a: eqtype) (f: Set.set a) (x: a) 
  : Lemma (ensures (mem x (of_set f) <==> Set.mem x f))
          [SMTPat (mem x (of_set f))]

(* extensionality *)

(*| Two sets with the same members are `FStar.GhostSet.equal`.

    Triggered automatically on `equal s1 s2`. *)
val lemma_equal_intro: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 = mem x s2))
    (ensures (equal s1 s2))
    [SMTPat (equal s1 s2)]

(*| Extensionality: `FStar.GhostSet.equal` sets are equal (`==`).

    Triggered automatically on `equal s1 s2`. To prove `s1 == s2`, it
    usually suffices to assert `equal s1 s2`. *)
val lemma_equal_elim: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (equal s1 s2))
    (ensures  (s1 == s2))
    [SMTPat (equal s1 s2)]

(*| Equal (`==`) sets are `FStar.GhostSet.equal`.

    Triggered automatically on `equal s1 s2`. *)
val lemma_equal_refl: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (s1 == s2))
    (ensures  (equal s1 s2))
    [SMTPat (equal s1 s2)]

(*| No element is a member of two disjoint sets.

    Triggered automatically on `disjoint s1 s2`; the resulting quantifier is
    triggered by `mem x s1` or `mem x s2`. *)
let disjoint_not_in_both (a:Type) (s1:set a) (s2:set a) :
  Lemma
    (requires (disjoint s1 s2))
    (ensures (forall (x:a).{:pattern (mem x s1) \/ (mem x s2)} mem x s1 ==> ~(mem x s2)))
  [SMTPat (disjoint s1 s2)]
= let f (x:a) : Lemma (~(mem x (intersect s1 s2))) = () in
  FStar.Classical.forall_intro f

(* Converting lists to sets *)

(*| The set of the elements of a list, as a union of singletons. *)
let rec as_set' (#a:Type) (l:list a) : set a = 
  match l with
  | [] -> empty
  | hd::tl -> union (singleton hd) (as_set' tl)

(*| A subset of a set disjoint from `s2` is disjoint from `s2`: if
    `disjoint s1 s2` and `subset s3 s1`, then `disjoint s3 s2`. *)
let lemma_disjoint_subset (#a:Type) (s1:set a) (s2:set a) (s3:set a)
  : Lemma (requires (disjoint s1 s2 /\ subset s3 s1))
          (ensures  (disjoint s3 s2))
  = ()
