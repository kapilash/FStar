(*
   Copyright 2008-2026 Microsoft Research

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
module FStar.Real.Dedekind

/// The real numbers, constructed as Dedekind cuts of [FStar.Rational.rat].
///
/// Unlike [FStar.Real], which is a logical model of Z3's theory of reals and is
/// therefore entirely axiomatized, everything in this module is *constructed*:
/// [real] is a concrete type, the operations are concrete definitions, and
/// every law below is proved.  The only assumptions used are the two standard
/// logical axioms already present in F*'s library --- functional and
/// propositional extensionality --- which are what make "equality of cuts" be
/// F*'s propositional equality [==]. No property of the reals is assumed.
///
/// The representation is sealed by this interface: a real is *characterized* by
/// the ordered-field laws plus completeness ([lub]) below, which is exactly what
/// a client needs.

module Q = FStar.Rational

(*| The real numbers, constructed as Dedekind cuts of `FStar.Rational.rat`.

    Unlike the SMT-interpreted `FStar.Real.real`, everything here is a definition and every law is proved, using only functional and propositional extensionality and classical logic. The representation (an erased `FStar.Real.Dedekind.Base.cut`) is sealed: a real is characterized by the ordered-field laws and completeness (`FStar.Real.Dedekind.lub`) of this module. Erasable, so reals are only usable in specifications and proofs.

    The laws are lemmas to be called explicitly; none has an SMT pattern.

    ```fstar
    let sum_comm4 (a b c d:D.real)
      : Lemma (D.add (D.add a b) (D.add c d) == D.add (D.add c d) (D.add a b)) =
      D.add_comm (D.add a b) (D.add c d)
    ``` *)
[@@erasable]
val real : Type0

(**** The rational numbers sit inside the reals *)

(*| The embedding of the rationals into the reals: `of_rat r` is the cut of rationals strictly below `r`.

    A morphism of ordered fields: see `FStar.Real.Dedekind.of_rat_add`, `FStar.Real.Dedekind.of_rat_mul`, `FStar.Real.Dedekind.of_rat_opp`, `FStar.Real.Dedekind.of_rat_lt` and `FStar.Real.Dedekind.of_rat_inj`. *)
val of_rat : Q.rat -> real

(*| The embedding of the integers into the reals, through `FStar.Rational.of_int`. *)
let of_int (n:int) : real = of_rat (Q.of_int n)

(*| The real `0`, defined as `of_int 0`. *)
let zero : real = of_int 0
(*| The real `1`, defined as `of_int 1`. *)
let one  : real = of_int 1
(*| The real `2`, defined as `of_int 2`. *)
let two  : real = of_int 2

(**** Order *)

(*| Strict order on reals, as a proposition: `lt x y` holds when the cut of `x` is strictly contained in the cut of `y`.

    A strict total order (`FStar.Real.Dedekind.lt_irrefl`, `FStar.Real.Dedekind.lt_trans`, `FStar.Real.Dedekind.lt_total`), compatible with addition and multiplication by positives. *)
val lt : real -> real -> prop

(*| Non-strict order on reals: `lt x y \/ x == y`. *)
let le (x y:real) : prop = lt x y \/ x == y
(*| `gt x y` is `lt y x`. *)
let gt (x y:real) : prop = lt y x
(*| `ge x y` is `le y x`. *)
let ge (x y:real) : prop = le y x

(**** Field operations *)

(*| Addition of reals.

    Laws: `FStar.Real.Dedekind.add_comm`, `FStar.Real.Dedekind.add_assoc`, `FStar.Real.Dedekind.add_zero`, `FStar.Real.Dedekind.add_opp`. *)
val add : real -> real -> real
(*| Negation (additive inverse) of a real. See `FStar.Real.Dedekind.add_opp`. *)
val opp : real -> real
(*| Multiplication of reals.

    Laws: `FStar.Real.Dedekind.mul_comm`, `FStar.Real.Dedekind.mul_assoc`, `FStar.Real.Dedekind.mul_one`, `FStar.Real.Dedekind.mul_zero`, `FStar.Real.Dedekind.distrib`, `FStar.Real.Dedekind.mul_inv`. *)
val mul : real -> real -> real

(*| Multiplicative inverse of a real, made total by setting `inv zero == zero`.

    `FStar.Real.Dedekind.mul_inv` gives `mul x (inv x) == one` for `x =!= zero`. *)
val inv : real -> real

(*| Subtraction of reals, `add x (opp y)`. *)
let sub (x y:real) : real = add x (opp y)
(*| Division of reals, `mul x (inv y)`.

    Total: dividing by `zero` gives `zero`, because `inv zero == zero`. *)
let div (x y:real) : real = mul x (inv y)

(**** Abelian group under addition *)

(*| Addition of reals is commutative: `add x y == add y x`. *)
val add_comm  (x y:real)   : Lemma (add x y == add y x)
(*| Addition of reals is associative: `add (add x y) z == add x (add y z)`. *)
val add_assoc (x y z:real) : Lemma (add (add x y) z == add x (add y z))
(*| `zero` is a right identity for addition: `add x zero == x`. *)
val add_zero  (x:real)     : Lemma (add x zero == x)
(*| `opp x` is an additive inverse of `x`: `add x (opp x) == zero`. *)
val add_opp   (x:real)     : Lemma (add x (opp x) == zero)

(**** Commutative monoid under multiplication, and a field *)

(*| Multiplication of reals is commutative: `mul x y == mul y x`. *)
val mul_comm  (x y:real)   : Lemma (mul x y == mul y x)
(*| Multiplication of reals is associative: `mul (mul x y) z == mul x (mul y z)`. *)
val mul_assoc (x y z:real) : Lemma (mul (mul x y) z == mul x (mul y z))
(*| `one` is a right identity for multiplication: `mul x one == x`. *)
val mul_one   (x:real)     : Lemma (mul x one == x)
(*| `zero` is absorbing for multiplication: `mul x zero == zero`. *)
val mul_zero  (x:real)     : Lemma (mul x zero == zero)

(*| Multiplication distributes over addition: `mul x (add y z) == add (mul x y) (mul x z)`. *)
val distrib (x y z:real)
  : Lemma (mul x (add y z) == add (mul x y) (mul x z))

(*| A nonzero real times its inverse is one: `mul x (inv x) == one` when `x =!= zero`. *)
val mul_inv (x:real)
  : Lemma (requires x =!= zero) (ensures mul x (inv x) == one)

(**** Total order, compatible with the field structure *)

(*| The order `lt` is irreflexive: `lt x x` is false. *)
val lt_irrefl (x:real)   : Lemma (~(lt x x))
(*| The order `lt` is transitive: `lt x y` and `lt y z` give `lt x z`. *)
val lt_trans  (x y z:real) : Lemma (requires lt x y /\ lt y z) (ensures lt x z)
(*| The order `lt` is total (trichotomy): `lt x y`, `x == y` or `lt y x`.

    Proved classically. *)
val lt_total  (x y:real) : Lemma (lt x y \/ x == y \/ lt y x)

(*| Adding the same real to both sides preserves and reflects the order: `lt (add x z) (add y z)` iff `lt x y`. *)
val lt_add_r (x y z:real)
  : Lemma (lt (add x z) (add y z) <==> lt x y)

(*| Multiplying both sides by a positive real `z` preserves and reflects the order: `lt (mul x z) (mul y z)` iff `lt x y`. *)
val lt_mul_pos (x y z:real)
  : Lemma (requires lt zero z) (ensures lt (mul x z) (mul y z) <==> lt x y)

(**** The embedding is a morphism of ordered fields *)

(*| `of_rat` preserves addition: `of_rat (Q.add p q) == add (of_rat p) (of_rat q)`. *)
val of_rat_add (p q:Q.rat) : Lemma (of_rat (Q.add p q) == add (of_rat p) (of_rat q))
(*| `of_rat` preserves multiplication: `of_rat (Q.mul p q) == mul (of_rat p) (of_rat q)`. *)
val of_rat_mul (p q:Q.rat) : Lemma (of_rat (Q.mul p q) == mul (of_rat p) (of_rat q))
(*| `of_rat` preserves negation: `of_rat (Q.neg p) == opp (of_rat p)`. *)
val of_rat_opp (p:Q.rat)   : Lemma (of_rat (Q.neg p) == opp (of_rat p))
(*| `of_rat` preserves and reflects the order: `lt (of_rat p) (of_rat q)` iff `Q.lt p q`. *)
val of_rat_lt  (p q:Q.rat) : Lemma (lt (of_rat p) (of_rat q) <==> Q.lt p q)
(*| `of_rat` is injective: `of_rat p == of_rat q` iff `p == q`. *)
val of_rat_inj (p q:Q.rat) : Lemma (of_rat p == of_rat q <==> p == q)

(**** Archimedes *)

(*| Archimedes' property: every real is strictly below some natural number `of_int n`.

    Equivalently, the rationals are dense in the reals. Proved from the construction, using `FStar.Rational.archimedean`. *)
val archimedean (x:real) : Lemma (exists (n:nat). lt x (of_int n))

(**** Completeness: the whole point of the construction *)

/// Sets of reals, as predicates.
(*| Sets of reals, represented as predicates `real -> prop`. *)
let rset = real -> prop

(*| `b` is an upper bound of the set `s`: every member `x` of `s` satisfies `le x b`. *)
let is_upper_bound (s:rset) (b:real) : prop = forall (x:real). s x ==> le x b
(*| The set `s` has some upper bound. *)
let is_bounded_above (s:rset) : prop = exists (b:real). is_upper_bound s b
(*| The set `s` has at least one member. *)
let is_nonempty (s:rset) : prop = exists (x:real). s x
(*| `b` is the least upper bound of `s`: an upper bound of `s` that is `le` every other upper bound. *)
let is_lub (s:rset) (b:real) : prop =
  is_upper_bound s b /\ (forall (c:real). is_upper_bound s c ==> le b c)

(*| The least upper bound of a nonempty set of reals that is bounded above.

    Completeness is what distinguishes the reals from the rationals. It is proved, not assumed: the bound is the union of the cuts in the set (see `FStar.Real.Dedekind.Sup.csup`). Ghost, because the set is an arbitrary predicate. `FStar.Real.lub` exposes it for `FStar.Real.real`, and `FStar.Math.Sqrt` uses it to define a square root without an axiom. *)
val lub (s:rset)
  : Ghost real
      (requires is_nonempty s /\ is_bounded_above s)
      (ensures  fun b -> is_lub s b)
