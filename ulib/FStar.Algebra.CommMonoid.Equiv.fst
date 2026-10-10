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
module FStar.Algebra.CommMonoid.Equiv


(*| An equivalence relation on `a`, packaged with proofs of its laws.

    The single constructor `EQ` has the fields:

    - `eq`: the relation, a `prop`-valued binary predicate.
    - `reflexivity`: a proof of `eq x x`.
    - `symmetry`: a proof that `eq x y` implies `eq y x`.
    - `transitivity`: a proof that `eq x y` and `eq y z` imply `eq x z`.

    `FStar.Algebra.CommMonoid.Equiv.equality_equiv` is propositional equality.
    `FStar.Algebra.CommMonoid.Equiv.elim_eq_laws` exposes the laws as
    quantified facts for the SMT solver. *)
unopteq
type equiv (a:Type) =
  | EQ :
    eq:(a -> a -> prop) -> 
    reflexivity:(x:a -> Lemma (x `eq` x)) ->
    symmetry:(x:a -> y:a -> Lemma (requires (x `eq` y)) (ensures (y `eq` x))) ->
    transitivity:(x:a -> y:a -> z:a -> Lemma (requires (x `eq` y /\ y `eq` z)) (ensures (x `eq` z))) ->
    equiv a

(*| Brings the reflexivity, symmetry and transitivity of `eq.eq` into the
    proof context as quantified facts with SMT patterns.

    Call it once at the start of a proof that needs to chain equivalences
    without invoking the individual law fields. The quantifiers trigger on
    `eq.eq x y` terms (transitivity on a pair `eq.eq x y` and `eq.eq y z`). *)
let elim_eq_laws #a (eq:equiv a)
  : Lemma (
          (forall x.{:pattern (x `eq.eq` x)} x `eq.eq` x) /\
          (forall x y.{:pattern (x `eq.eq` y)} x `eq.eq` y ==> y `eq.eq` x) /\
          (forall x y z.{:pattern eq.eq x y; eq.eq y z} (x `eq.eq` y /\ y `eq.eq` z) ==> x `eq.eq` z)
          )
  = introduce forall x. x `eq.eq` x
    with (eq.reflexivity x);

    introduce forall x y. x `eq.eq` y ==> y `eq.eq` x
    with (introduce _ ==> _
          with eq.symmetry x y);

    introduce forall x y z. (x `eq.eq` y /\ y `eq.eq` z) ==> x `eq.eq` z
    with (introduce _ ==> _
          with eq.transitivity x y z)

(*| Propositional equality `==` on `a`, as an `FStar.Algebra.CommMonoid.Equiv.equiv`.

    Use it to state a commutative monoid whose laws hold up to `==`, as in
    `FStar.Algebra.CommMonoid.Equiv.int_plus_cm`. *)
let equality_equiv (a:Type) : equiv a =
  EQ (fun x y -> x == y) (fun x -> ()) (fun x y -> ()) (fun x y z -> ())

(*| A commutative monoid on `a` whose laws hold up to the equivalence `eq`.

    The single constructor `CM` has the fields:

    - `unit`: the neutral element.
    - `mult`: the binary operation.
    - `identity`: a proof that `mult unit x` is equivalent to `x` (left identity).
    - `associativity`: a proof that `mult (mult x y) z` is equivalent to `mult x (mult y z)`.
    - `commutativity`: a proof that `mult x y` is equivalent to `mult y x`.
    - `congruence`: a proof that `mult` respects `eq` in both arguments.

    Right identity follows; see `FStar.Algebra.CommMonoid.Equiv.right_identity`.
    This is the structure used by `FStar.Seq.Permutation.foldm_snoc`,
    `FStar.Algebra.CommMonoid.Fold.fold` and `FStar.Matrix`. With
    `FStar.Algebra.CommMonoid.Equiv.equality_equiv` it coincides with
    `FStar.Algebra.CommMonoid.cm` plus a trivial congruence. *)
unopteq
type cm (a:Type) (eq:equiv a) =
  | CM :
    unit:a ->
    mult:(a -> a -> a) ->
    identity : (x:a -> Lemma ((unit `mult` x) `EQ?.eq eq` x)) ->
    associativity : (x:a -> y:a -> z:a ->
                      Lemma ((x `mult` y `mult` z) `EQ?.eq eq` (x `mult` (y `mult` z)))) ->
    commutativity:(x:a -> y:a -> Lemma ((x `mult` y) `EQ?.eq eq` (y `mult` x))) ->
    congruence:(x:a -> y:a -> z:a -> w:a -> Lemma (requires (x `EQ?.eq eq` z /\ y `EQ?.eq eq` w)) (ensures ((mult x y) `EQ?.eq eq` (mult z w)))) ->
    cm a eq



// temporarily fixing the universe of this lemma to u#1 because 
// otherwise tactics for LowStar.Resource canonicalization fails
// by picking up an incorrect universe u#0 for resource type
(*| Proves that the unit of `m` is also a right identity: `mult x unit` is
    equivalent to `x` under `eq`.

    Derived from the `identity`, `commutativity` and `transitivity` laws; call
    it explicitly. *)
let right_identity (#a:Type u#aa) (eq:equiv a) (m:cm a eq) (x:a)
  : Lemma (x `CM?.mult m` (CM?.unit m) `EQ?.eq eq` x) = 
  CM?.commutativity m x (CM?.unit m); 
  CM?.identity m x;
  EQ?.transitivity eq (x `CM?.mult m` (CM?.unit m)) ((CM?.unit m) `CM?.mult m` x) x

(*| The commutative monoid of integers under addition, with unit `0`, up to
    propositional equality. *)
let int_plus_cm : cm int (equality_equiv int) =
  CM 0 (+) (fun _ -> ()) (fun _ _ _ -> ()) (fun _ _ -> ()) (fun _ _ _ _ -> ())

(*| The commutative monoid of integers under multiplication, with unit `1`, up
    to propositional equality. *)
let int_multiply_cm : cm int (equality_equiv int) =
  CM 1 ( * ) (fun _ -> ()) (fun _ _ _ -> ()) (fun _ _ -> ()) (fun _ _ _ _ -> ())
