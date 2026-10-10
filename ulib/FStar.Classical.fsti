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

module FStar.Classical

/// This module provides various utilities to manipulate the
/// logical connectives [==>], [/\], [\/], [forall], [exists] and [==],
/// defined in Prims.
///
/// - [Lemma p] is also a proof-irrelevant proof of [p], expressed as
///   a postcondition of a unit-returning Ghost computation.

(**** Implication *)

(*| Turns a proof of the implication `a ==> b` into a function from proofs of
    `a` to proofs of `b`.

    The converse of `FStar.Classical.arrow_to_impl`. *)
val impl_to_arrow (#a #b: prop) : (a ==> b) -> (a -> b)

(*| Turns a function from proofs of `a` to proofs of `b` into a proof of the
    implication `a ==> b`.

    The converse of `FStar.Classical.impl_to_arrow`. For a function in the
    `Lemma` effect, use `FStar.Classical.impl_intro`. *)
val arrow_to_impl (#a #b: prop) : (a -> b) -> (a ==> b)

(*| Proves the implication `p ==> q` from a function from proofs of `p` to
    proofs of `q`.

    Like `FStar.Classical.arrow_to_impl`, but the `$` argument must have
    exactly the expected type, which helps infer `p` and `q`. For a function
    in the `Lemma` effect, use `FStar.Classical.impl_intro`. *)
val impl_intro_gtot (#p #q: prop) ($_: (p -> q)) : (p ==> q)

(*| Proves the implication `p ==> q` from a total function from proofs of `p`
    to proofs of `q`.

    The same as `FStar.Classical.impl_intro_gtot`, for a function in the `Tot`
    effect. *)
val impl_intro_tot (#p #q: prop) ($_: (p -> q)) : (p ==> q)

(*| Proves the implication `p ==> q` from a lemma that, given a proof of `p`,
    ensures `q`.

    To turn a lemma with a `requires` clause into an implication, use
    `FStar.Classical.move_requires`. *)
val impl_intro (#p #q: prop) ($_: (p -> Lemma q)) : Lemma (p ==> q)

(*| Turns a lemma with precondition `p x` and postcondition `q x` into one
    with no precondition that ensures `p x ==> q x`.

    Useful for calling a lemma where its precondition may not hold, or for
    passing it to `FStar.Classical.forall_intro`, which requires lemmas
    without preconditions. Variants for 2 to 4 arguments are
    `FStar.Classical.move_requires_2` to `FStar.Classical.move_requires_4`.

    ```fstar
    let pos_square (x: int)
      : Lemma (requires x > 0) (ensures x * x > 0)
      = ()

    let square_if_pos (x: int) : Lemma (x > 0 ==> x * x > 0) =
      FStar.Classical.move_requires pos_square x
    ``` *)
val move_requires
      (#a: Type)
      (#p #q: (a -> prop))
      ($_: (x: a -> Lemma (requires (p x)) (ensures (q x))))
      (x: a)
    : Lemma (p x ==> q x)

(*| `FStar.Classical.move_requires` for a lemma with 2 arguments: ensures
    `p x y ==> q x y`. *)
val move_requires_2
      (#a: Type)
      (#b: (a -> Type))
      (#p #q: (x: a -> b x -> prop))
      ($_: (x: a -> y: b x -> Lemma (requires (p x y)) (ensures (q x y))))
      (x: a)
      (y: b x)
    : Lemma (p x y ==> q x y)

(*| `FStar.Classical.move_requires` for a lemma with 3 arguments: ensures
    `p x y z ==> q x y z`. *)
val move_requires_3
      (#a: Type)
      (#b: (a -> Type))
      (#c: (x: a -> y: b x -> Type))
      (#p #q: (x: a -> y: b x -> c x y -> prop))
      ($_: (x: a -> y: b x -> z: c x y -> Lemma (requires (p x y z)) (ensures (q x y z))))
      (x: a)
      (y: b x)
      (z: c x y)
    : Lemma (p x y z ==> q x y z)

(*| `FStar.Classical.move_requires` for a lemma with 4 arguments: ensures
    `p x y z w ==> q x y z w`. *)
val move_requires_4
      (#a: Type)
      (#b: (a -> Type))
      (#c: (x: a -> y: b x -> Type))
      (#d: (x: a -> y: b x -> z: c x y -> Type))
      (#p #q: (x: a -> y: b x -> z: c x y -> w: d x y z -> prop))
      ($_: (x: a -> y: b x -> z: c x y -> w: d x y z -> Lemma (requires (p x y z w)) (ensures (q x y z w))))
      (x: a)
      (y: b x)
      (z: c x y)
      (w: d x y z)
    : Lemma (p x y z w ==> q x y z w)

(*| Proves `p ==> q ()` when the statement `q` is only well formed under the
    assumption `p`.

    `q` takes a proof of `p` as an argument, so it can mention terms whose
    types need `p`. The lemma argument proves `q ()` given `p`. *)
val impl_intro_gen (#p: prop) (#q: p -> prop) (_: (p -> Lemma (q ())))
    : Lemma (p ==> q ())

(**** Universal quantification *)

/// Many of the utilities for universal quantification are designed to
/// help in the proofs of lemmas that ensure quantified
/// postconditions. For example, in order to prove [Lemma (forall
/// (x:a). p x)] it is often useful to "get your hands" on a freshly
/// introduced variable [x] and to prove [p x] for it, i.e., to prove
/// [x:a -> Lemma (p x)] and to turn this into a proof for [forall
/// x. p x]. Functions like [forall_intro] in this module let you do
/// just that.
///
/// That said, it may often be more convenient to prove such
/// properties using local lemmas in inner scopes. For example, here
/// are two proof sketches for [forall x. p x].
///
/// {[
///    assume
///    val p : nat -> prop
///
///    let proof1 =
///      let lem (x:nat)
///        : Lemma (ensures p x)
///        = admit()
///      in
///      forall_intro lem;
///      assert (forall x. p x)
///
///    let proof2 =
///      let lem (x:nat)
///        : Lemma (ensures p x)
///                [SMTPat (p x)]
///        = admit()
///      in
///      assert (forall x. p x)
/// ]}
///
/// In [proof1], we prove an auxiliary lemma [lem] and then use
/// [forall_intro] to turn it into a proof of [forall x. p x].
///
/// In [proof2], we simply decorate [lem] with an SMT pattern to
/// allow the solver to use that lemma to prove [forall x. p x]
/// directly.
///
/// The style of [proof2] is often more robust for several reasons:
///
///  - [forall_intro] only works with lemmas that do not have
///    preconditions. E.g., if you wanted to prove [forall x. q x ==>
///    p x], you would have had to prove [lem] with the type [x:nat ->
///    Lemma (q x ==> p x)]. In contrast, in the style of [proof2],
///    you could have proven [x:nat -> Lemma (requires q x) (ensures p
///    x)], which is easier, since you can assume the precondition [q
///    x]. To use this style of lemma-with-precondition with
///    [forall_intro], one typically must also use [move_requires] to
///    coerce a lemma with a precondition into a lemma proving an
///    implication, or to use [ghost_lemma].
///
///  - [forall_intro] introduces a quantifier without an SMT
///    pattern. This can pollute the local context with an unguarded
///    quantifier, leading to inefficient proofs. Note, the variants
///    [forall_intro_with_pat] help with this somewhat, but they only
///    support a single pattern, rather than conjunctive and
///    disjunctive patterns.
///
///  - [forall_intro] and its variants are available for only a fixed
///    arity up to 4. The nested SMTPat lemma style of [proof2] works
///    are arbitrary arity.
///
/// That said, there may still be cases where [forall_intro] etc. are
/// more suitable.

(*| Proves `forall x. p x` from a function that returns a proof of `p x` for
    every `x`.

    The result is the proof itself, a value of the quantified type. To get
    the same fact as a `Lemma`, use `FStar.Classical.lemma_forall_intro_gtot`. *)
val forall_intro_gtot (#a: Type) (#p: a -> prop) ($_: (x: a -> p x))
    : forall (x: a). p x

(*| Proves `forall x. p x`, as a `Lemma`, from a function that returns a proof
    of `p x` for every `x`.

    `FStar.Classical.forall_intro_gtot` gives the same proof as a value. *)
val lemma_forall_intro_gtot (#a: Type) (#p: a -> prop) ($_: (x: a -> p x))
    : Lemma (forall (x: a). p x)

(*| Turns a function returning a proof of `p x` into a lemma ensuring `p x`,
    for the given `x`. *)
val gtot_to_lemma (#a: Type) (#p: a -> prop) ($_: (x: a -> p x)) (x: a) : Lemma (p x)

(* TODO: perhaps remove this? *)
(*| Proves `forall x. p x` from a function that returns a proof of `p x` for
    every `x`.

    Has the same type as `FStar.Classical.forall_intro_gtot`, which is
    preferable. *)
val forall_intro_squash_gtot (#a: Type) (#p: a -> prop) ($_: (x: a -> p x))
    : forall (x: a). p x

(*| Proves `forall x. p x` from a ghost function that returns a proof of
    `p x` for every `x`.

    Like `FStar.Classical.forall_intro_squash_gtot`, but the argument may be
    ghost. *)
val forall_intro_squash_gtot_join
      (#a: Type)
      (#p: a -> prop)
      ($_: (x: a -> GTot (p x)))
    : (forall (x: a). p x)

(*| Proves `forall x. p x` from a lemma that ensures `p x` for any `x`.

    The main way to establish a universally quantified postcondition. The
    lemma must have no precondition; to use one with a `requires` clause,
    first apply `FStar.Classical.move_requires`, or use
    `FStar.Classical.ghost_lemma`. The quantifier gets no SMT pattern; for one,
    use `FStar.Classical.forall_intro_with_pat`. Variants for 2 to 4 bound
    variables are `FStar.Classical.forall_intro_2` to
    `FStar.Classical.forall_intro_4`.

    A local lemma with an SMT pattern is often a more robust alternative: it
    supports preconditions, any number of variables, and any patterns.

    ```fstar
    let double_nonneg (x: nat) : Lemma (x + x >= 0) = ()

    let all_doubles_nonneg () : Lemma (forall (x: nat). x + x >= 0) =
      FStar.Classical.forall_intro double_nonneg
    ``` *)
val forall_intro (#a: Type) (#p: (a -> prop)) ($_: (x: a -> Lemma (p x)))
    : Lemma (forall (x: a). p x)

(*| Proves `forall x. p x` from a lemma that ensures `p x` for any `x`, with
    `pat x` as the quantifier's SMT pattern.

    Supports a single pattern only, not conjunctive or disjunctive patterns.
    Otherwise the same as `FStar.Classical.forall_intro`. *)
val forall_intro_with_pat
      (#a: Type)
      (#c: (x: a -> Type))
      (#p: (x: a -> prop))
      ($pat: (x: a -> c x))
      ($_: (x: a -> Lemma (p x)))
    : Lemma (forall (x: a). {:pattern (pat x)} p x)

(*| Proves `forall x. p x` from a lemma that ensures `p x` for any `x`,
    allowing subtyping on the lemma's type.

    `FStar.Classical.forall_intro` requires the lemma's type to unify with the
    expected type, which helps infer `p`. This variant checks it by subtyping
    instead, so `p` and other implicit arguments usually have to be given
    explicitly. *)
val forall_intro_sub (#a: Type) (#p: (a -> prop)) (_: (x: a -> Lemma (p x)))
    : Lemma (forall (x: a). p x)

(*| `FStar.Classical.forall_intro` for two bound variables: proves
    `forall x y. p x y` from a lemma ensuring `p x y`. *)
val forall_intro_2
      (#a: Type)
      (#b: (a -> Type))
      (#p: (x: a -> b x -> prop))
      ($_: (x: a -> y: b x -> Lemma (p x y)))
    : Lemma (forall (x: a) (y: b x). p x y)

(*| `FStar.Classical.forall_intro_with_pat` for two bound variables: proves
    `forall x y. p x y` with `pat x y` as the SMT pattern. *)
val forall_intro_2_with_pat
      (#a: Type)
      (#b: (a -> Type))
      (#c: (x: a -> y: b x -> Type))
      (#p: (x: a -> b x -> prop))
      ($pat: (x: a -> y: b x -> Tot (c x y)))
      ($_: (x: a -> y: b x -> Lemma (p x y)))
    : Lemma (forall (x: a) (y: b x). {:pattern (pat x y)} p x y)

(*| `FStar.Classical.forall_intro` for three bound variables: proves
    `forall x y z. p x y z` from a lemma ensuring `p x y z`. *)
val forall_intro_3
      (#a: Type)
      (#b: (a -> Type))
      (#c: (x: a -> y: b x -> Type))
      (#p: (x: a -> y: b x -> z: c x y -> prop))
      ($_: (x: a -> y: b x -> z: c x y -> Lemma (p x y z)))
    : Lemma (forall (x: a) (y: b x) (z: c x y). p x y z)

(*| `FStar.Classical.forall_intro_with_pat` for three bound variables: proves
    `forall x y z. p x y z` with `pat x y z` as the SMT pattern. *)
val forall_intro_3_with_pat
      (#a: Type)
      (#b: (a -> Type))
      (#c: (x: a -> y: b x -> Type))
      (#d: (x: a -> y: b x -> z: c x y -> Type))
      (#p: (x: a -> y: b x -> z: c x y -> prop))
      ($pat: (x: a -> y: b x -> z: c x y -> Tot (d x y z)))
      ($_: (x: a -> y: b x -> z: c x y -> Lemma (p x y z)))
    : Lemma (forall (x: a) (y: b x) (z: c x y). {:pattern (pat x y z)} p x y z)

(*| `FStar.Classical.forall_intro` for four bound variables: proves
    `forall x y z w. p x y z w` from a lemma ensuring `p x y z w`. *)
val forall_intro_4
      (#a: Type)
      (#b: (a -> Type))
      (#c: (x: a -> y: b x -> Type))
      (#d: (x: a -> y: b x -> z: c x y -> Type))
      (#p: (x: a -> y: b x -> z: c x y -> w: d x y z -> prop))
      ($_: (x: a -> y: b x -> z: c x y -> w: d x y z -> Lemma (p x y z w)))
    : Lemma (forall (x: a) (y: b x) (z: c x y) (w: d x y z). p x y z w)

(* TODO: Seems overly specific; could be removed? *)
(*| Proves `forall x. p x ==> q x` from a lemma that, given `x` and a proof of
    `p x`, ensures `q x`.

    Combines `FStar.Classical.arrow_to_impl` with
    `FStar.Classical.forall_intro`. *)
val forall_impl_intro
      (#a: Type)
      (#p #q: (a -> prop))
      ($_: (x: a -> p x -> Lemma (q x)))
    : Lemma (forall x. p x ==> q x)

(* Note: It's unclear why [q] has an additional [unit] argument. *)
(*| Proves `forall x. p x ==> q x ()` from a lemma with precondition `p x` and
    postcondition `q x ()`.

    Like `FStar.Classical.forall_intro`, but for a lemma with a precondition. *)
val ghost_lemma
      (#a: Type)
      (#p: (a -> prop))
      (#q: (a -> unit -> prop))
      ($_: (x: a -> Lemma (requires p x) (ensures (q x ()))))
    : Lemma (forall (x: a). p x ==> q x ())


(**** Existential quantification *)

(*| Proves `exists x. p x` from a witness `witness` for which `p witness`
    holds.

    There are no variants for several bound variables. To prove
    `exists x y. p x y`, one can prove `exists xy. p (fst xy) (snd xy)` with a
    pair as the witness and let the SMT solver convert it. *)
val exists_intro (#a: Type) (p: (a -> prop)) (witness: a)
    : Lemma (requires (p witness)) (ensures (exists (x: a). p x))

(*| Proves `exists x. p x` classically: from a proof that `~(p x)` for every
    `x` would lead to a contradiction. *)
val exists_intro_not_all_not
      (#a: Type)
      (#p: (a -> prop))
      ($f: ((x: a -> Lemma (~(p x))) -> Lemma False))
    : Lemma (exists x. p x)

(*| Proves `(exists x. p x) ==> r` from a lemma that ensures `p x ==> r` for
    every `x`. *)
val forall_to_exists (#a: Type) (#p: (a -> prop)) (#r: prop) ($_: (x: a -> Lemma (p x ==> r)))
    : Lemma ((exists (x: a). p x) ==> r)

(* TODO: overly specific, remove? *)
(*| `FStar.Classical.forall_to_exists` for two independent existential
    hypotheses: proves `((exists x. p x) /\ (exists y. q y)) ==> r`. *)
val forall_to_exists_2
      (#a: Type)
      (#p: (a -> prop))
      (#b: Type)
      (#q: (b -> prop))
      (#r: prop)
      ($f: (x: a -> y: b -> Lemma ((p x /\ q y) ==> r)))
    : Lemma (((exists (x: a). p x) /\ (exists (y: b). q y)) ==> r)

(*| Eliminates an existential: proves `goal` from a proof of `exists x. p x`
    and a function that proves `goal` from any `x` with `p x`. *)
val exists_elim
      (goal: prop) (#a: Type)
      (#p: (a -> prop))
      (_: (exists (x: a). p x))
      (_: (x: a{p x} -> GTot goal))
    : Lemma goal


(*** Disjunction *)

(*| Eliminates a disjunction: proves `(l \/ r) ==> goal ()` from lemmas
    proving `goal ()` assuming `l` and assuming `r`.

    `goal` takes a proof of `l \/ r` as an argument, so its well-formedness may
    depend on the disjunction. *)
val or_elim
      (#l #r: prop)
      (#goal: ((l \/ r) -> prop))
      (hl: (l -> Lemma (goal ())))
      (hr: (r -> Lemma (goal ())))
    : Lemma ((l \/ r) ==> goal ())

(*| The law of excluded middle: `p \/ ~p` holds for any proposition `p`. *)
val excluded_middle (p: prop) : Lemma (ensures (p \/ ~p))
