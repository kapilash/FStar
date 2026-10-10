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
module FStar.Real
(*
  This module provides a signature for real arithmetic.

  Real number constants can be specific in floating point format with
  an 'R' suffix, e.g., 1.0R

  All these operations are mapped to the corresponding primitives
  in Z3's theory of real arithmetic.

  This is only a logical model of the reals. There is no extraction
  for them, as they are an erasable type. Any operation that can observe
  a real (comparisons, etc) must be Ghost or a proposition.

  Unlike most SMT-mapped theories in F*, this one is not merely assumed:
  [FStar.Real.fst] *implements* everything declared here in terms of
  [FStar.Real.Dedekind], the reals built from scratch as Dedekind cuts of
  [FStar.Rational]. So [real] is a concrete type, the field operations are
  concrete definitions.

  This is exactly the arrangement [FStar.BV] has with [FStar.BitVector]: the
  symbols below are still given Z3's native interpretation by the SMT
  encoding --- that is what makes real-arithmetic goals discharge
  automatically, and it does mean that the *identification* of this type with
  Z3's [Real] sort remains an assumption of the encoding --- but there is now
  a construction underneath witnessing that the assumed theory has a model.

  Having a construction underneath also lets this interface state things Z3
  cannot prove. Z3's reals form an ordered *field*; what makes the reals *the*
  reals is completeness, and [lub] below exposes it as a theorem of the
  Dedekind construction. [FStar.Math.Sqrt] uses nothing but [lub] to define an
  axiom-free square root, discharging the axiom it used to assume.

  Note that the [FStar.Real.Dedekind] hierarchy is deliberately *not* visible
  in this interface: [FStar.Real] is a dependency of the reflection stubs, and
  hence of essentially all of F*, so its interface is kept as light as it has
  always been. The construction is a dependency of [FStar.Real.fst] only.
*)

(*| The real numbers, as a logical (erasable) type for specifications and proofs.

    Literals are written with an `R` suffix, as in `1.0R`. The operations of this module are interpreted by the SMT encoding as Z3's native theory of real arithmetic, so goals in the theory of ordered fields are usually discharged automatically. That identification with Z3's reals is an assumption of the encoding; underneath, `FStar.Real.fst` defines `real` and its operations as the Dedekind reals of `FStar.Real.Dedekind`, which shows the assumed theory has a model and provides the completeness results `FStar.Real.lub` and `FStar.Real.archimedean`.

    `real` is erasable: there is no extraction, so any computation that observes a real must be ghost or a proposition.

    ```fstar
    let _ = assert (1.0R +. 1.0R == 2.0R)
    let _ = assert (forall (x:real). x >. 0.0R ==> x /. 2.0R <. x)
    ``` *)
[@@erasable]
val real : Type0

(*| The embedding of the integers into the reals.

    When its argument is an integer literal, the normalizer folds it to the corresponding real literal. *)
val of_int : int -> Tot real

(*| Addition of reals, interpreted by Z3's real addition. *)
val ( +. ) : real -> real -> Tot real
(*| Subtraction of reals, interpreted by Z3's real subtraction. *)
val ( -. ) : real -> real -> Tot real
(*| Multiplication of reals, interpreted by Z3's real multiplication. *)
val ( *. ) : real -> real -> Tot real
(*| Division of reals; the divisor must be provably different from `0.0R`.

    Interpreted by Z3's real division. *)
val ( /. ) : real -> d:real{d =!= 0.0R} -> Tot real

(*| Strict order on reals, `x >. y`, as a proposition.

    Not a boolean: comparisons of reals cannot be computed. *)
val ( >.  ) : real -> real -> prop
(*| Non-strict order on reals, `x >=. y`, as a proposition. *)
val ( >=. ) : real -> real -> prop

(*| Strict order on reals, `x <. y`, as a proposition.

    Not a boolean: comparisons of reals cannot be computed. *)
val ( <.  ) : real -> real -> prop
(*| Non-strict order on reals, `x <=. y`, as a proposition. *)
val ( <=. ) : real -> real -> prop

(*| The real `0`, defined as `of_int 0`. *)
let zero : real = of_int 0
(*| The real `1`, defined as `of_int 1`. *)
let one  : real = of_int 1
(*| The real `2`, defined as `of_int 2`. *)
let two  : real = of_int 2

(**** Completeness *)

/// Z3's theory of reals is a theory of ordered *fields*: it says nothing at
/// all about completeness, so nothing below can be discharged by SMT. It is
/// instead *proved* in [FStar.Real.fst], where [real] is the type of Dedekind
/// cuts of [FStar.Rational] and the least upper bound is a construction.
///
/// This is what makes [real] the reals rather than some arbitrary ordered
/// field, and it is what [FStar.Math.Sqrt] uses to define a square root
/// without assuming one.

(*| Sets of reals, represented as predicates `real -> prop`. *)
let rset = real -> prop

(*| `b` is an upper bound of the set `s`: every member `x` of `s` satisfies `x <=. b`. *)
let is_upper_bound (s:rset) (b:real) : prop = forall (x:real). s x ==> x <=. b
(*| The set `s` has some upper bound. *)
let is_bounded_above (s:rset) : prop = exists (b:real). is_upper_bound s b
(*| The set `s` has at least one member. *)
let is_nonempty (s:rset) : prop = exists (x:real). s x
(*| `b` is the least upper bound of `s`: an upper bound of `s` that is `<=.` every other upper bound. *)
let is_lub (s:rset) (b:real) : prop =
  is_upper_bound s b /\ (forall (c:real). is_upper_bound s c ==> b <=. c)

(*| The least upper bound of a nonempty set of reals that is bounded above.

    This is completeness, the property that distinguishes the reals from other ordered fields. Z3's theory of reals does not include it, so it cannot be obtained by SMT; here it is a theorem, transferred from `FStar.Real.Dedekind.lub`. `FStar.Math.Sqrt` uses it to define a square root without an axiom. Ghost, since the bound is chosen classically. *)
val lub (s:rset)
  : Ghost real
      (requires is_nonempty s /\ is_bounded_above s)
      (ensures  fun b -> is_lub s b)

(*| Archimedes' property: every real is strictly below some natural number `of_int n`.

    Proved from the Dedekind construction, `FStar.Real.Dedekind.archimedean`. *)
val archimedean (x:real) : Lemma (exists (n:nat). x <. of_int n)
