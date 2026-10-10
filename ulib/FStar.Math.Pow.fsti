module FStar.Math.Pow

open FStar.Real

(*| Strictly positive reals, the bases accepted by `FStar.Math.Pow.pow`. *)
type rpos = a:real{a >. 0.0R}

(*| Real exponentiation `a` to the `x`, for a strictly positive base and any
    real exponent.

    Constructed from least upper bounds in `FStar.Real` (no axioms beyond those
    of the reals). Zero and negative bases are excluded because their powers
    are not defined for every real exponent. Reals are erased, so `pow` is for
    specifications and proofs only. `FStar.Math.Pow.exp2` fixes the base `2`. *)
val pow (a:rpos) (x:real) : rpos

(*| `pow a x` is strictly positive. *)
val pow_positive (a:rpos) (x:real) : Lemma (pow a x >. 0.0R)
(*| Any base to the exponent `0.0R` is `1.0R`. *)
val pow_zero (a:rpos) : Lemma (pow a 0.0R == 1.0R)
(*| Any base to the exponent `1.0R` is itself. *)
val pow_one (a:rpos) : Lemma (pow a 1.0R == a)
(*| The base `1.0R` to any exponent is `1.0R`. *)
val pow_one_base (x:real) : Lemma (pow 1.0R x == 1.0R)

(*| A negated exponent gives the reciprocal:
    `pow a (0.0R -. x) == 1.0R /. pow a x`. *)
val pow_neg (a:rpos) (x:real)
  : Lemma (pow a (0.0R -. x) == 1.0R /. pow a x)
(*| Inverting the base inverts the power:
    `pow (1.0R /. a) x == 1.0R /. pow a x`. *)
val pow_inverse_base (a:rpos) (x:real)
  : Lemma (pow (1.0R /. a) x == 1.0R /. pow a x)

(*| Integer exponents obey the usual recurrence `a^(n+1) = a * a^n`, for every
    integer `n`, including negative ones. *)
val pow_succ (a:rpos) (n:int)
  : Lemma (pow a (of_int (n+1)) == a *. pow a (of_int n))

(*| Rational exponents are roots: for `n > 0`, raising `pow a (m / n)` to the
    `n` gives `pow a m`. *)
val pow_rational (a:rpos) (m:nat) (n:pos)
  : Lemma (pow (pow a (of_int m /. of_int n)) (of_int n) == pow a (of_int m))

(*| The positive `n`-th root of `a^m` is unique: any positive `r` with
    `pow r n == pow a m` equals `pow a (m / n)`. *)
val pow_rational_unique (a:rpos) (m:nat) (n:pos) (r:rpos)
  : Lemma (requires pow r (of_int n) == pow a (of_int m))
          (ensures pow a (of_int m /. of_int n) == r)

(*| Exponentiation by one half agrees with `FStar.Math.Sqrt.sqrt`. *)
val pow_half (a:rpos) : Lemma (pow a 0.5R == FStar.Math.Sqrt.sqrt a)

(*| For a base at least `1.0R`, `pow a x` is nondecreasing in the exponent. *)
val pow_mono (a:real{a >=. 1.0R}) (x y:real{x <=. y})
  : Lemma (pow a x <=. pow a y)

(*| For a base between `0.0R` (exclusive) and `1.0R` (inclusive), `pow a x` is
    nonincreasing in the exponent. *)
val pow_antitone (a:real{0.0R <. a /\ a <=. 1.0R}) (x y:real{x <=. y})
  : Lemma (pow a y <=. pow a x)

(*| Raising a power to another exponent multiplies the exponents:
    `pow (pow a x) y == pow a (x *. y)`. *)
val pow_pow (a:rpos) (x y:real)
  : Lemma (pow (pow a x) y == pow a (x *. y))

(*| Real powers of two: `exp2 x` is `pow 2.0R x`. *)
let exp2 (x:real) : rpos = pow 2.0R x
