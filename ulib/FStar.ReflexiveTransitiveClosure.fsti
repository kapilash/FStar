(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.ReflexiveTransitiveClosure

/// This module defines the reflexive transitive closure of a
/// relation. That is, the smallest preorder that includes it.
///
/// Closures are convenient for defining monotonic memory references:
///
/// - Define a `step` relation and take `closure step` as the
///   monotonic relation of the reference.
///
/// - To witness a property of the value of the reference, one must
///   show that the property is stable with respect to `closure step`,
///   but this boils down to proving that is stable with respect to
///   `step` (see lemma `stable_on_closure` below).
///
/// See examples/preorder/Closure.fst for usage examples.

(*| A binary relation on `a`, as a `prop`-valued function. *)
let binrel (a:Type) = a -> a -> prop

(*| A predicate on `a`, as a `prop`-valued function. *)
let predicate (a:Type u#a) = a -> prop

(*| Holds when `rel` relates every element to itself. *)
let reflexive (#a:Type) (rel:binrel u#a a) =
  forall (x:a). rel x x

(*| Holds when `rel x y` and `rel y z` imply `rel x z` for all `x`, `y`, `z`. *)
let transitive (#a:Type) (rel:binrel u#a a) =
  forall (x:a) (y:a) (z:a). (rel x y /\ rel y z) ==> rel x z

(*| Holds when `rel` is reflexive and transitive. *)
let preorder_rel (#a:Type) (rel:binrel u#a a) =
  reflexive rel /\ transitive rel

(*| The type of preorders on `a`: relations that are reflexive and transitive. *)
type preorder (a:Type u#a) : Type u#a = rel:binrel u#a a{preorder_rel rel}

(*| Holds when the predicate `p` is preserved along `rel`: `p x` and `rel x y`
    imply `p y`.

    See `FStar.ReflexiveTransitiveClosure.stable_on_closure` to prove this for a
    closure. *)
let stable (#a:Type u#a) (p:a -> prop) (rel:binrel u#a a{preorder_rel rel}) =
  forall (x:a) (y:a). (p x /\ rel x y) ==> p y

(*| The reflexive transitive closure of `r`: the smallest preorder that
    includes `r`.

    `closure r x y` holds when `y` can be reached from `x` in zero or more `r`
    steps. It is abstract; reason about it with
    `FStar.ReflexiveTransitiveClosure.closure_step`,
    `FStar.ReflexiveTransitiveClosure.closure_inversion`,
    `FStar.ReflexiveTransitiveClosure.stable_on_closure` and
    `FStar.ReflexiveTransitiveClosure.induct`. A typical use is as the
    monotonicity relation of a monotonic reference, defined from a single-step
    relation. *)
val closure (#a:Type u#a) (r:binrel u#a a) : preorder u#a a

(*| `closure r` includes `r`: `r x y` implies `closure r x y`.

    Triggered automatically on `closure r x y`. *)
val closure_step: #a:Type u#a -> r:binrel u#a a -> x:a -> y:a { r x y }
  -> Lemma (ensures closure r x y)
    [SMTPat (closure r x y)]

(*| Inversion for the closure: if `closure r x y`, then either `x == y`, or
    there is a `z` with `r x z` and `closure r z y`. *)
val closure_inversion: #a:Type u#a -> r:binrel u#a a -> x:a -> y:a
  -> Lemma (requires closure r x y)
          (ensures  x == y \/ (exists z. r x z /\ closure r z y))

(*| A predicate that is stable along `r` is stable along `closure r`: if `p x`
    and `r x y` imply `p y`, then `p x` and `closure r x y` imply `p y`.

    The resulting quantifier is triggered by `closure r x y`. This is useful
    to witness properties of monotonic references whose relation is the
    closure of a step relation.

    ```fstar
    let incr_step (x y: int) : prop = y == x + 1

    let incr_closure_monotone (x y: int)
      : Lemma (requires FStar.ReflexiveTransitiveClosure.closure incr_step x y)
              (ensures x <= y) =
      FStar.ReflexiveTransitiveClosure.stable_on_closure incr_step (fun z -> x <= z) ()
    ``` *)
val stable_on_closure: #a:Type u#a -> r:binrel u#a a -> p:(a -> prop)
  -> p_stable_on_r: (squash (forall x y.{:pattern (p y); (r x y)} p x /\ (r x y) ==> p y))
  -> Lemma (forall x y.{:pattern (closure r x y)} p x /\ (closure r x y) ==> p y)

(*| Induction over the reflexive transitive closure of `r`: a relation `p`
    that is reflexive, contains `r` and is transitive holds of every pair in
    `closure r`. *)
val induct
      (#a:Type) (r:binrel a) (p: a -> a -> prop)
      (f_refl: (x:a -> squash (p x x)))
      (f_step: (x:a -> y:a { r x y } -> squash (p x y)))
      (f_closure: (x:a -> y:a -> z:a { p x y /\ p y z } -> squash (p x z)))
      (x:a) (y:a) (xy:squash (closure r x y))
: squash (p x y)

