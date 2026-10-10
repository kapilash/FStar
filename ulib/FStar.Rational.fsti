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
module FStar.Rational

/// The ordered field of rational numbers, developed without any axiom.
///
/// Rationals are represented canonically (as a fraction in lowest terms with a
/// positive denominator), so F*'s propositional equality [==] on [rat] *is*
/// equality of rationals. That is what makes [rat] usable as the index type of
/// a Dedekind cut; see [FStar.Real.Dedekind].
///
/// The representation is abstract: clients reason through [num]/[den] and the
/// [mk_*] congruences, or, more usually, through the field and order laws.

module L = FStar.Math.Lemmas

(*| Multiplication of positive integers, returning `a * b` with its positivity in the result type.

    Used to build denominators (see `FStar.Rational.mk_add` and `FStar.Rational.mk_mul`) without a separate positivity lemma. *)
val pmul (a b:pos) : c:pos{c == a * b}

(*| The type of rational numbers, with decidable equality.

    Every rational is stored canonically, as a fraction in lowest terms with a positive denominator, so propositional equality `==` and boolean equality `=` on `rat` are equality of rationals. This is what lets `rat` index the Dedekind cuts of `FStar.Real.Dedekind`. The representation is abstract: build values with `FStar.Rational.mk` or `FStar.Rational.of_int`, inspect them with `FStar.Rational.num` and `FStar.Rational.den`, and reason with the field and order laws of this module. Everything is proved; no axiom is used. *)
val rat : eqtype

(**** Representation *)

(*| The numerator of a rational in lowest terms.

    The sign of a rational is carried by its numerator. See `FStar.Rational.den`. *)
val num : rat -> int
(*| The denominator of a rational in lowest terms, always positive.

    The denominator of zero is `1` (see `FStar.Rational.num_den_reduced`). *)
val den : rat -> pos

(*| The rational `n/d`, for any integer `n` and positive denominator `d`.

    The fraction is normalized to lowest terms, so `mk 2 4 == mk 1 2`. Use `FStar.Rational.mk_eq` to decide equality of two `mk` terms and `FStar.Rational.mk_cross` to relate `mk n d` to its numerator and denominator. *)
val mk (n:int) (d:pos) : rat

(*| Rebuilding a rational from its numerator and denominator gives it back: `mk (num q) (den q) == q`.

    Triggered automatically on `mk (num q) (den q)`. *)
val mk_num_den (q:rat) : Lemma (mk (num q) (den q) == q) [SMTPat (mk (num q) (den q))]

(*| Zero has denominator `1`: if `num q == 0` then `den q == 1`. *)
val num_den_reduced (q:rat) : Lemma (num q == 0 ==> den q == 1)

(*| Two rationals are equal exactly when they cross-multiply equally: `p == q` iff `num p * den q == num q * den p`. *)
val eq_cross (p q:rat)
  : Lemma (p == q <==> num p * den q == num q * den p)

(*| `mk n d` denotes `n/d`: its numerator and denominator cross-multiply with `n` and `d`, `num (mk n d) * d == n * den (mk n d)`.

    The numerator and denominator themselves may differ from `n` and `d`, since `mk` reduces the fraction. *)
val mk_cross (n:int) (d:pos)
  : Lemma (num (mk n d) * d == n * den (mk n d))

(*| Two fractions denote the same rational exactly when they cross-multiply equally: `mk n1 d1 == mk n2 d2` iff `n1 * d2 == n2 * d1`. *)
val mk_eq (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (mk n1 d1 == mk n2 d2 <==> n1 * d2 == n2 * d1)

(**** Embedding of the integers *)

(*| The embedding of the integers into the rationals, `n` as `n/1`.

    It preserves addition, multiplication and the order and is injective: see `FStar.Rational.of_int_add`, `FStar.Rational.of_int_mul`, `FStar.Rational.of_int_lt` and `FStar.Rational.of_int_inj`. *)
val of_int (n:int) : rat

(*| The rational `of_int n` has numerator `n` and denominator `1`. *)
val of_int_num_den (n:int) : Lemma (num (of_int n) == n /\ den (of_int n) == 1)

(*| `of_int n` is the fraction `mk n 1`. *)
val of_int_mk (n:int) : Lemma (of_int n == mk n 1)

(*| The rational `0`, defined as `of_int 0`. *)
let zero : rat = of_int 0
(*| The rational `1`, defined as `of_int 1`. *)
let one  : rat = of_int 1
(*| The rational `2`, defined as `of_int 2`. *)
let two  : rat = of_int 2

(**** Field operations *)

(*| Addition of rationals.

    Computed on representatives by `FStar.Rational.mk_add`; its laws are `FStar.Rational.add_comm`, `FStar.Rational.add_assoc`, `FStar.Rational.add_zero` and `FStar.Rational.add_neg`. *)
val add : rat -> rat -> rat
(*| Negation (additive inverse) of a rational.

    Computed on representatives by `FStar.Rational.mk_neg`. See `FStar.Rational.add_neg` and `FStar.Rational.neg_neg`. *)
val neg : rat -> rat
(*| Multiplication of rationals.

    Computed on representatives by `FStar.Rational.mk_mul`; its laws are `FStar.Rational.mul_comm`, `FStar.Rational.mul_assoc`, `FStar.Rational.mul_one`, `FStar.Rational.mul_zero` and `FStar.Rational.distrib`. *)
val mul : rat -> rat -> rat

(*| Multiplicative inverse of a rational, made total by setting `inv zero == zero`.

    `FStar.Rational.inv_num_den` gives `mul q (inv q) == one` for `q =!= zero`. See also `FStar.Rational.div`. *)
val inv : rat -> rat

(*| Subtraction of rationals, `add p (neg q)`. *)
let sub (p q:rat) : rat = add p (neg q)
(*| Division of rationals, `mul p (inv q)`.

    Total: dividing by `zero` gives `zero`, because `inv zero == zero`. *)
let div (p q:rat) : rat = mul p (inv q)

(**** Order *)

(*| Strict order on rationals, as a boolean test.

    Computed on representatives by `FStar.Rational.mk_lt`. It is a strict total order (`FStar.Rational.lt_irrefl`, `FStar.Rational.lt_trans`, `FStar.Rational.lt_total`) compatible with addition and with multiplication by positives. *)
val lt : rat -> rat -> bool

(*| Non-strict order on rationals: `lt p q || p = q`. *)
let le (p q:rat) : bool = lt p q || p = q
(*| `gt p q` is `lt q p`. *)
let gt (p q:rat) : bool = lt q p
(*| `ge p q` is `le q p`. *)
let ge (p q:rat) : bool = le q p

(**** The [mk] congruences: every operation acts on representatives *)

(*| Addition on fractions: `add (mk n1 d1) (mk n2 d2) == mk (n1 * d2 + n2 * d1) (pmul d1 d2)`.

    Together with `FStar.Rational.mk_eq` this computes sums of concrete fractions.

    ```fstar
    let half_plus_half () : Lemma (Q.add (Q.mk 1 2) (Q.mk 1 2) == Q.one) =
      Q.mk_add 1 2 1 2;
      Q.of_int_mk 1;
      Q.mk_eq 4 4 1 1
    ``` *)
val mk_add (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (add (mk n1 d1) (mk n2 d2) == mk (n1 * d2 + n2 * d1) (pmul d1 d2))

(*| Negation on fractions: `neg (mk n d) == mk (-n) d`. *)
val mk_neg (n:int) (d:pos)
  : Lemma (neg (mk n d) == mk (-n) d)

(*| Multiplication on fractions: `mul (mk n1 d1) (mk n2 d2) == mk (n1 * n2) (pmul d1 d2)`. *)
val mk_mul (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (mul (mk n1 d1) (mk n2 d2) == mk (n1 * n2) (pmul d1 d2))

(*| Order on fractions: `lt (mk n1 d1) (mk n2 d2)` iff `n1 * d2 < n2 * d1`. *)
val mk_lt (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (lt (mk n1 d1) (mk n2 d2) <==> n1 * d2 < n2 * d1)

(*| A nonzero rational times its inverse is one: `mul q (inv q) == one` when `q =!= zero`. *)
val inv_num_den (q:rat)
  : Lemma (requires q =!= zero)
          (ensures  mul q (inv q) == one)

(**** Field laws *)

(*| Addition of rationals is commutative: `add p q == add q p`. *)
val add_comm (p q:rat)     : Lemma (add p q == add q p)
(*| Addition of rationals is associative: `add (add p q) r == add p (add q r)`. *)
val add_assoc (p q r:rat)  : Lemma (add (add p q) r == add p (add q r))
(*| `zero` is a right identity for addition: `add p zero == p`. *)
val add_zero (p:rat)       : Lemma (add p zero == p)
(*| `neg p` is an additive inverse of `p`: `add p (neg p) == zero`. *)
val add_neg (p:rat)        : Lemma (add p (neg p) == zero)
(*| Negation is an involution: `neg (neg p) == p`. *)
val neg_neg (p:rat)        : Lemma (neg (neg p) == p)

(*| Multiplication of rationals is commutative: `mul p q == mul q p`. *)
val mul_comm (p q:rat)     : Lemma (mul p q == mul q p)
(*| Multiplication of rationals is associative: `mul (mul p q) r == mul p (mul q r)`. *)
val mul_assoc (p q r:rat)  : Lemma (mul (mul p q) r == mul p (mul q r))
(*| `one` is a right identity for multiplication: `mul p one == p`. *)
val mul_one (p:rat)        : Lemma (mul p one == p)
(*| `zero` is absorbing for multiplication: `mul p zero == zero`. *)
val mul_zero (p:rat)       : Lemma (mul p zero == zero)
(*| Negation commutes with multiplication: `mul (neg p) q == neg (mul p q)`. *)
val mul_neg (p q:rat)      : Lemma (mul (neg p) q == neg (mul p q))

(*| Multiplication distributes over addition: `mul p (add q r) == add (mul p q) (mul p r)`. *)
val distrib (p q r:rat)
  : Lemma (mul p (add q r) == add (mul p q) (mul p r))

(*| The rationals have no zero divisors: `mul p q == zero` iff `p == zero` or `q == zero`. *)
val mul_eq_zero (p q:rat)
  : Lemma (mul p q == zero <==> (p == zero \/ q == zero))

(**** Order laws *)

(*| The order `lt` is irreflexive: `lt p p` is false. *)
val lt_irrefl (p:rat)     : Lemma (~(lt p p))
(*| The order `lt` is transitive: `lt p q` and `lt q r` give `lt p r`. *)
val lt_trans (p q r:rat)  : Lemma (requires lt p q /\ lt q r) (ensures lt p r)
(*| The order `lt` is total (trichotomy): `lt p q`, `p == q` or `lt q p`. *)
val lt_total (p q:rat)    : Lemma (lt p q \/ p == q \/ lt q p)
(*| The order `lt` is asymmetric: `lt p q` excludes `lt q p`. *)
val lt_asym (p q:rat)     : Lemma (requires lt p q) (ensures ~(lt q p))

(*| Adding the same rational to both sides preserves and reflects the order: `lt (add p r) (add q r)` iff `lt p q`. *)
val lt_add_r (p q r:rat)  : Lemma (lt (add p r) (add q r) <==> lt p q)
(*| Negation reverses the order: `lt (neg q) (neg p)` iff `lt p q`. *)
val lt_neg (p q:rat)      : Lemma (lt (neg q) (neg p) <==> lt p q)

(*| Multiplying both sides by a positive rational `r` preserves and reflects the order: `lt (mul p r) (mul q r)` iff `lt p q`. *)
val lt_mul_pos (p q r:rat)
  : Lemma (requires lt zero r) (ensures lt (mul p r) (mul q r) <==> lt p q)

(*| The product of two positive rationals is positive. *)
val mul_pos (p q:rat)
  : Lemma (requires lt zero p /\ lt zero q) (ensures lt zero (mul p q))

(*| The inverse of a positive rational is positive. *)
val inv_pos (p:rat)
  : Lemma (requires lt zero p) (ensures lt zero (inv p))

(**** Integers, floor, Archimedes, density *)

(*| `of_int` preserves addition: `of_int (m + n) == add (of_int m) (of_int n)`. *)
val of_int_add (m n:int) : Lemma (of_int (m + n) == add (of_int m) (of_int n))
(*| `of_int` preserves multiplication: `of_int (m * n) == mul (of_int m) (of_int n)`. *)
val of_int_mul (m n:int) : Lemma (of_int (m * n) == mul (of_int m) (of_int n))
(*| `of_int` preserves and reflects the order: `lt (of_int m) (of_int n)` iff `m < n`. *)
val of_int_lt  (m n:int) : Lemma (lt (of_int m) (of_int n) <==> m < n)
(*| `of_int` is injective: `of_int m == of_int n` iff `m == n`. *)
val of_int_inj (m n:int) : Lemma (of_int m == of_int n <==> m == n)

(*| The greatest integer less than or equal to `q`.

    Rounds toward negative infinity, also for negative `q`. Specified by `FStar.Rational.floor_spec`. *)
val floor (q:rat) : int

(*| `floor q` is the integer part of `q`: `of_int (floor q)` is at most `q`, and `q` is strictly below `of_int (floor q + 1)`. *)
val floor_spec (q:rat)
  : Lemma (le (of_int (floor q)) q /\ lt q (of_int (floor q + 1)))

(*| Archimedes' property: every rational is strictly below some natural number `of_int n`.

    Used to prove the completeness of `FStar.Real.Dedekind`. See also `FStar.Rational.small_inv`. *)
val archimedean (q:rat) : Lemma (exists (n:nat). lt q (of_int n))

(*| For every positive rational `eps` there is a positive integer `n` with `mk 1 n` (that is, `1/n`) strictly below `eps`. *)
val small_inv (eps:rat)
  : Lemma (requires lt zero eps)
          (ensures  exists (n:pos). lt (mk 1 n) eps)

(*| The midpoint `(p + q) / 2` of two rationals.

    `FStar.Rational.mid_spec` shows it lies strictly between `p` and `q` when `lt p q`, witnessing that the order is dense. *)
val mid (p q:rat) : rat

(*| When `lt p q`, the midpoint `mid p q` lies strictly between `p` and `q`. *)
val mid_spec (p q:rat)
  : Lemma (requires lt p q) (ensures lt p (mid p q) /\ lt (mid p q) q)

(*| A rational strictly below `q`, namely `q - 1`.

    Used to show that Dedekind cuts are nonempty. See also `FStar.Rational.above`. *)
val below (q:rat) : r:rat{lt r q}

(*| A rational strictly above `q`, namely `q + 1`.

    See also `FStar.Rational.below`. *)
val above (q:rat) : r:rat{lt q r}
