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
*)
module FStar.PCM

/// This module defines the partial commutative monoid (PCM) algebraic structure, as well as helper
/// predicates and functions to manipulate PCMs.

(**** Base definitions *)

(*| The type of symmetric binary relations on `a`: `prop`-valued relations `c`
    with `c x y <==> c y x`.

    Used for the `composable` field of `FStar.PCM.pcm'`. *)
let symrel (a: Type u#a) = c:(a -> a -> prop) { (forall x y. c x y <==> c y x) }

(*| The carrier of a partial commutative monoid, without its laws.

    A record with the fields:

    - `composable`: a symmetric relation telling which pairs of elements can be combined.
    - `op`: the partial operation, defined on composable pairs only.
    - `one`: the unit element.

    `FStar.PCM.pcm` adds the laws. *)
noeq
type pcm' (a:Type u#a) = {
  composable: symrel a;
  op: x:a -> y:a{composable x y} -> a;
  one:a
}

(*| The type of proofs that the operation of `p` is commutative on composable
    pairs: `p.op x y == p.op y x`. *)
let lem_commutative (#a: Type u#a) (p:pcm' a) =
  x:a ->
  y:a{p.composable x y} ->
    Lemma (p.op x y == p.op y x)

(*| The type of proofs of associativity, from right-nested to left-nested: if
    `x` composes with `p.op y z`, then `x` composes with `y`, `p.op x y`
    composes with `z`, and `p.op x (p.op y z) == p.op (p.op x y) z`. *)
let lem_assoc_l (#a: Type u#a) (p:pcm' a) =
  x:a ->
  y:a ->
  z:a{p.composable y z /\ p.composable x (p.op y z)} ->
  Lemma (p.composable x y /\
         p.composable (p.op x y) z /\
         p.op x (p.op y z) == p.op (p.op x y) z)


(*| The type of proofs of associativity, from left-nested to right-nested: if
    `p.op x y` composes with `z`, then `y` composes with `z`, `x` composes
    with `p.op y z`, and the two groupings are equal. *)
let lem_assoc_r (#a: Type u#a) (p:pcm' a) =
  x:a ->
  y:a ->
  z:a {p.composable x y /\
       p.composable (p.op x y) z} ->
  Lemma
      (p.composable y z /\
       p.composable x (p.op y z) /\
       p.op x (p.op y z) == p.op (p.op x y) z)

(*| The type of proofs that `p.one` is a unit: every `x` composes with `p.one`,
    and `p.op x p.one == x`. *)
let lem_is_unit (#a: Type u#a) (p:pcm' a) =
  x:a ->
  Lemma (p.composable x p.one /\
         p.op x p.one == x)

(*| A partial commutative monoid (PCM) on `a`, the algebraic structure of
    separable resources used by separation-logic frameworks such as Steel and
    Pulse.

    A record with the fields:

    - `p`: the carrier, of type `FStar.PCM.pcm'` (composability, operation, unit).
    - `comm`: commutativity, `FStar.PCM.lem_commutative`.
    - `assoc`: associativity, `FStar.PCM.lem_assoc_l`.
    - `assoc_r`: associativity in the other direction, `FStar.PCM.lem_assoc_r`.
    - `is_unit`: the unit law, `FStar.PCM.lem_is_unit`.
    - `refine`: a predicate on the full values that can be stored; frame-preserving updates must preserve it.

    Use `FStar.PCM.composable` and `FStar.PCM.op` rather than projecting the
    fields of `p`. *)
noeq
type pcm (a:Type u#a) = {
  p:pcm' a;
  comm:lem_commutative p;
  assoc: lem_assoc_l p;
  assoc_r: lem_assoc_r p;
  is_unit: lem_is_unit p;
  refine: a -> prop
}

(**** Derived predicates *)


(*| Holds when `x` and `y` can be combined with the operation of `p`.

    A symmetric relation; the field `composable` of the carrier `p.p`. *)
let composable (#a: Type u#a) (p:pcm a) (x y:a) = p.p.composable x y

(*| Combines two composable elements with the operation of `p`.

    The caller must prove `composable p x y`. *)
let op (#a: Type u#a) (p:pcm a) (x:a) (y:a{composable p x y}) = p.p.op x y

(*| Holds when `x` is a fragment of `y`: there is a `frame` composable with `x`
    such that `op pcm frame x == y`.

    In separation-logic terms, knowledge `x` is compatible with the full value
    `y`. Compatibility is reflexive (`FStar.PCM.compatible_refl`) and
    transitive (`FStar.PCM.compatible_trans`). Use `FStar.PCM.compatible_intro`
    and `FStar.PCM.compatible_elim` to introduce and eliminate the existential. *)
let compatible (#a: Type u#a) (pcm:pcm a) (x y:a) =
  (exists (frame:a).
    composable pcm x frame /\ op pcm frame x == y
  )

(*| Proves that every element is compatible with itself, using the unit as
    the frame. *)
let compatible_refl
  (#a: Type u#a) (pcm:pcm a) (x:a)
    : Lemma (compatible pcm x x)
  =
  pcm.is_unit x;
  pcm.comm x pcm.p.one;
  assert (op pcm pcm.p.one x == x)

(*| Proves that compatibility is transitive: if `x` is compatible with `y` and
    `y` with `z`, then `x` is compatible with `z`. *)
let compatible_trans
  (#a: Type u#a) (pcm:pcm a) (x y z:a)
  : Lemma (requires (compatible pcm x y /\ compatible pcm y z))
          (ensures (compatible pcm x z))
  = Classical.forall_intro_3 pcm.assoc

(*| Eliminates `compatible pcm x y`: proves `goal` from a lemma that
    establishes it for any frame with `composable pcm x frame` and
    `op pcm frame x == y`.

    Use it to name the existentially quantified frame inside a proof. *)
let compatible_elim
  (#a: Type u#a) (pcm:pcm a) (x y:a)
  (goal: prop)
  (lemma: (frame: a{composable pcm x frame /\ op pcm frame x == y}) ->
    Lemma (goal)
  )
    : Lemma (requires (compatible pcm x y)) (ensures (goal))
  =
  Classical.exists_elim
    goal #a #(fun frame -> composable pcm x frame /\ op pcm frame x == y)
    () (fun frame -> lemma frame)
    
(*| Proves `compatible pcm x y` from an explicit `frame` with
    `composable pcm x frame` and `op pcm frame x == y`. *)
let compatible_intro
  (#a: Type u#a) (pcm:pcm a) (x y:a)
  (frame: a)
  : Lemma
    (requires (composable pcm x frame /\ op pcm frame x == y))
    (ensures (compatible pcm x y))
  = ()

(*| Holds when `x` and `y` can evolve to a common point: some `z` is compatible
    with both. *)
let joinable #a (p:pcm a) (x y : a) : prop =
  exists z. compatible p x z /\ compatible p y z

(*| Holds when every frame that composes with `x` to give `v` also composes
    with `y` to give `v`.

    That is, replacing `x` by `y` preserves the frames of `x` within the value
    `v`. The quantifier has the SMT pattern `composable p x frame`. *)
let frame_compatible #a (p:pcm a) (x:FStar.Ghost.erased a) (v y:a) =
  (forall (frame:a). {:pattern (composable p x frame)}
            composable p x frame /\
            v == op p x frame ==>
            composable p y frame /\
            v == op p y frame)


(*| The type of frame-preserving updates from `x` to `y`: functions that turn a
    full value into a new full value without disturbing any frame.

    Given a value `v` that satisfies `p.refine` and is compatible with `x`, the
    update returns a value `v_new` that satisfies `p.refine`, is compatible
    with `y`, and such that every frame composable with `x` is composable with
    `y`, and if `op p x frame == v` then `op p y frame == v_new`. The
    quantifier has the SMT pattern `composable p x frame`.

    These are the updates that separation-logic frameworks allow on a
    reference holding a PCM value. See `FStar.PCM.no_op_is_frame_preserving`,
    `FStar.PCM.compose_frame_preserving_updates`,
    `FStar.PCM.frame_preserving_subframe` and
    `FStar.PCM.frame_preserving_val_to_fp_upd` for ways to build them. *)
type frame_preserving_upd (#a:Type u#a) (p:pcm a) (x y:a) =
  v:a{
    p.refine v /\
    compatible p x v
  } ->
  v_new:a{
    p.refine v_new /\
    compatible p y v_new /\
    (forall (frame:a{composable p x frame}).{:pattern composable p x frame}
       composable p y frame /\
       (op p x frame == v ==> op p y frame == v_new))}


(*| Holds when replacing `x` by `y` preserves all frames and `y` absorbs them:
    every frame composable with `x` is composable with `y`, and
    `op pcm frame y == y` for such frames.

    A special case in which the update from `x` to `y` can ignore the old
    value; see `FStar.PCM.frame_preserving_val_to_fp_upd`. The second
    quantifier has the SMT pattern `composable pcm frame x`. *)
let frame_preserving (#a: Type u#a) (pcm:pcm a) (x y: a) =
    (forall frame. composable pcm frame x ==> composable pcm frame y) /\
    (forall frame.{:pattern (composable pcm frame x)} composable pcm frame x ==> op pcm frame y == y)

(*| Builds the constant frame-preserving update from `x` to `v`, given that `v`
    satisfies `p.refine` and `FStar.PCM.frame_preserving p x v`.

    The update ignores the old value and returns `v`. *)
let frame_preserving_val_to_fp_upd (#a:Type u#a) (p:pcm a)
  (x:Ghost.erased a) (v:a{frame_preserving p x v /\ p.refine v})
  : frame_preserving_upd p x v
  = Classical.forall_intro (p.comm v);
    compatible_refl p v;
    assert (forall (y z:a). composable p y z <==> composable p z y);
    fun _ -> v

(*| Holds when `x` is exclusive in `p`: the only element composable with `x` is
    the unit `p.p.one`. *)
let exclusive (#a:Type u#a) (p:pcm a) (x:a) =
  forall (frame:a). composable p x frame ==> frame == p.p.one

(*| Proves that replacing an exclusive element `x` by the unit is frame
    preserving: `FStar.PCM.frame_preserving p x p.p.one`. *)
let exclusive_is_frame_preserving (#a: Type u#a) (p:pcm a) (x:a)
  : Lemma (requires exclusive p x)
          (ensures frame_preserving p x p.p.one)
  = p.is_unit x;
    p.is_unit p.p.one

(* Some sanity checks on the definition of frame preserving updates *)

(*| The identity update, a frame-preserving update from `x` to `x`. *)
let no_op_is_frame_preserving (#a:Type u#a) (p:pcm a)
  (x:a)
  : frame_preserving_upd p x x
  = fun v -> v

(*| Composes a frame-preserving update from `x` to `y` with one from `y` to
    `z`, giving a frame-preserving update from `x` to `z`. *)
let compose_frame_preserving_updates (#a:Type u#a) (p:pcm a)
  (x y z:a)
  (f:frame_preserving_upd p x y)
  (g:frame_preserving_upd p y z)
  : frame_preserving_upd p x z
  = fun v -> g (f v)

(*| Extends a frame-preserving update from `x` to `y` with a `subframe` that
    composes with both: the result updates `op p x subframe` to
    `op p y subframe`.

    The returned update applies `f` to the full value unchanged. *)
let frame_preserving_subframe (#a:Type u#a) (p:pcm a) (x y:a)
  (subframe:a{composable p x subframe /\ composable p y subframe})
  (f:frame_preserving_upd p x y)
  : frame_preserving_upd p (op p x subframe) (op p y subframe)
  = fun v ->
    compatible_elim p (op p x subframe) v (compatible p x v) (fun frame ->
      p.comm x subframe;
      p.assoc frame subframe x);
    let w = f v in
    let aux (frame: a{composable p (op p x subframe) frame}):
      Lemma (composable p (op p y subframe) frame /\
             (op p (op p x subframe) frame == v ==> op p (op p y subframe) frame == w))
             [SMTPat (composable p (op p y subframe) frame)]
    = p.assoc_r x subframe frame;
      assert (composable p x (op p subframe frame));
      assert (composable p y (op p subframe frame));
      p.assoc y subframe frame
    in
    compatible_elim p (op p x subframe) v (compatible p (op p y subframe) w) (fun frame ->
      aux frame;
      p.comm frame (op p x subframe);
      p.comm (op p y subframe) frame);
    w

