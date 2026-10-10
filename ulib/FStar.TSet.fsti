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
(** Propositional sets (on any types): membership is a predicate *)
module FStar.TSet

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(*| The type of sets of elements of any type, with membership given by a
    proposition.

    `FStar.TSet.mem` returns a `prop`, so membership need not be decidable and
    cannot be tested in code; the type is erasable, so sets exist only for
    specification and proofs. Sets may be infinite. Compare sets with
    `FStar.TSet.equal`, which is extensional.

    Related modules: `FStar.Set` is the variant for an `eqtype` with
    decidable boolean membership; `FStar.GSet` is the variant for any type,
    with ghost boolean membership. `FStar.TSet.tset_of_set` converts from
    `FStar.Set.set`. *)
[@@erasable]
val set (a:Type u#a) : Type u#a

(*| Extensional equality of sets: `equal s1 s2` holds when `s1` and `s2` have
    the same members.

    `FStar.TSet.lemma_equal_intro` and `FStar.TSet.lemma_equal_elim` (both
    triggered automatically on `equal s1 s2`) make it interchangeable with
    `==`. *)
val equal (#a:Type) (s1:set a) (s2:set a) : prop

(* destructors *)

(*| The proposition that `x` is a member of `s`.

    The membership lemmas such as `FStar.TSet.mem_union` describe how each
    operation affects it. *)
val mem : 'a -> set 'a -> prop

(* constructors *)
(*| The set with no members (see `FStar.TSet.mem_empty`). *)
val empty      : #a:Type -> Tot (set a)
(*| The set whose only member is `x` (see `FStar.TSet.mem_singleton`). *)
val singleton  : #a:Type -> x:a -> Tot (set a)
(*| The set of elements that are members of either argument (see
    `FStar.TSet.mem_union`). *)
val union      : #a:Type -> x:set a -> y:set a -> Tot (set a)
(*| The set of elements that are members of both arguments (see
    `FStar.TSet.mem_intersect`). *)
val intersect  : #a:Type -> x:set a -> y:set a -> Tot (set a)
(*| The set of all elements that are not members of the argument (see
    `FStar.TSet.mem_complement`). *)
val complement : #a:Type -> x:set a -> Tot (set a)
(*| The set whose members are the elements satisfying the predicate `f` (see
    `FStar.TSet.mem_intension`).

    Unlike `FStar.Set.intension`, the result is not ghost and the predicate
    need not be decidable. *)
val intension  : #a:Type -> (a -> prop) -> Tot (set a)

(* ops *)
(*| `subset s1 s2` holds when every member of `s1` is a member of `s2`. *)
let subset (#a:Type) (s1:set a) (s2:set a) : prop = forall x. mem x s1 ==> mem x s2

(* Properties *)
(*| No element is a member of `FStar.TSet.empty`.

    Triggered automatically on `mem x empty`. *)
val mem_empty: #a:Type -> x:a -> Lemma
   (requires True)
   (ensures (~ (mem x empty)))
   [SMTPat (mem x empty)]

(*| `y` is a member of `singleton x` exactly when `x == y`.

    Triggered automatically on `mem y (singleton x)`. *)
val mem_singleton: #a:Type -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (singleton x) <==> (x==y)))
   [SMTPat (mem y (singleton x))]

(*| Membership in `union s1 s2` is the disjunction of membership in `s1` and
    in `s2`.

    Triggered automatically on `mem x (union s1 s2)`. *)
val mem_union: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (union s1 s2) == (mem x s1 \/ mem x s2)))
   [SMTPat (mem x (union s1 s2))]

(*| Membership in `intersect s1 s2` is the conjunction of membership in `s1`
    and in `s2`.

    Triggered automatically on `mem x (intersect s1 s2)`. *)
val mem_intersect: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (intersect s1 s2) == (mem x s1 /\ mem x s2)))
   [SMTPat (mem x (intersect s1 s2))]

(*| Membership in `complement s` is the negation of membership in `s`.

    Triggered automatically on `mem x (complement s)`. *)
val mem_complement: #a:Type -> x:a -> s:set a -> Lemma
   (requires True)
   (ensures (mem x (complement s) == ~(mem x s)))
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

(*| Membership of `x` in `intension f` is the proposition `f x`.

    Triggered automatically on `mem x (intension f)`. *)
val mem_intension (#a:Type) (x:a) (f:(a -> prop))
: Lemma 
  (ensures (mem x (intension f) == f x))
  [SMTPat (mem x (intension f))]

(* extensionality *)

(*| Two sets with the same members are `FStar.TSet.equal`.

    Triggered automatically on `equal s1 s2`. *)
val lemma_equal_intro: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 <==> mem x s2))
    (ensures (equal s1 s2))
    [SMTPat (equal s1 s2)]

(*| Sets that are `FStar.TSet.equal` are equal (`==`): extensionality for sets.

    Triggered automatically on `equal s1 s2`. *)
val lemma_equal_elim: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (equal s1 s2))
    (ensures  (s1 == s2))
    [SMTPat (equal s1 s2)]

(*| Equal (`==`) sets are `FStar.TSet.equal`.

    Triggered automatically on `equal s1 s2`. *)
val lemma_equal_refl: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (s1 == s2))
    (ensures  (equal s1 s2))
    [SMTPat (equal s1 s2)]

(*| Converts a `FStar.Set.set` into a `FStar.TSet.set` with the same members
    (see `FStar.TSet.lemma_mem_tset_of_set`). *)
val tset_of_set (#a:eqtype) (s:Set.set a) : Tot (set a)

(*| An element is a member of `tset_of_set s` exactly when it is a member of
    the `FStar.Set.set` `s`.

    Triggered automatically on `mem x (tset_of_set s)`. *)
val lemma_mem_tset_of_set (#a:eqtype) (s:Set.set a) (x:a)
  :Lemma (requires True)
         (ensures  (Set.mem x s <==> mem x (tset_of_set s)))
         [SMTPat (mem x (tset_of_set s))]

(*| The set of members of `s` that satisfy the predicate `f` (see
    `FStar.TSet.lemma_mem_filter`). *)
val filter (#a:Type) (f:a -> prop) (s:set a) : Tot (set a)

(*| `x` is a member of `filter f s` exactly when it is a member of `s` and
    satisfies `f`.

    Triggered automatically on `mem x (filter f s)`. *)
val lemma_mem_filter (#a:Type) (f:(a -> prop)) (s:set a) (x:a)
  :Lemma (requires True)
         (ensures  (mem x (filter f s) <==> mem x s /\ f x))
         [SMTPat (mem x (filter f s))]

(*| The image of `s` under `f`: the set of values `f y` for members `y` of `s`
    (see `FStar.TSet.lemma_mem_map`). *)
val map (#a:Type) (#b:Type) (f:a -> Tot b) (s:set a) : Tot (set b)

(*| `x` is a member of `map f s` exactly when `x == f y` for some member `y` of
    `s`.

    Triggered automatically on `mem x (map f s)`. *)
val lemma_mem_map (#a:Type) (#b:Type) (f:(a -> Tot b)) (s:set a) (x:b)
  :Lemma ((exists (y:a). {:pattern (mem y s)} mem y s /\ x == f y) <==> mem x (map f s))
         [SMTPat (mem x (map f s))]

#reset-options
(*| Returns the set of the elements of a list, by structural recursion on the
    list.

    Unlike `FStar.Set.as_set`, there is no normalizing wrapper in this module. *)
let rec as_set' (#a:Type) (l:list a) : Tot (set a) =
  match l with
  | [] -> empty
  | hd::tl -> union (singleton hd) (as_set' tl)


(* unfold let as_set (#a:Type) (l:list a) : set a = *)
(*   Prims.norm [zeta; iota; delta_only ["FStar.TSet.as_set'"]] (as_set' l) *)
