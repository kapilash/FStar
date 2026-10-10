module FStar.Math.Sqrt

open FStar.Real

(*| Nonnegative reals, the domain and range of `FStar.Math.Sqrt.sqrt`. *)
type rnonneg = x:real{x >=. 0.0R}
(*| Strictly positive reals. *)
type rpos = x:real{x >. 0.0R}

(*| The nonnegative square root of a nonnegative real.

    This is a definition, not an axiom: `sqrt x` is the least upper bound of
    the nonnegative `y` with `y *. y <=. x`, which exists because `FStar.Real`
    is complete (see `FStar.Real.lub`). Z3's theory of reals has no square
    roots. Use `FStar.Math.Sqrt.sqrt_square` to get `sqrt x *. sqrt x == x`. *)
val sqrt (x : rnonneg) : rnonneg

(*| The square of `sqrt x` is `x`.

    Triggered automatically on `sqrt x *. sqrt x`. *)
val sqrt_square (x : rnonneg)
  : Lemma (ensures sqrt x *. sqrt x == x)
          [SMTPat (sqrt x *. sqrt x)]

(*| `sqrt x` is the only nonnegative `y` with `y *. y == x`.

    The main way to compute `sqrt` of a known square. *)
val sqrt_unique (x : rnonneg) (y : rnonneg)
  : Lemma (requires y *. y == x)
          (ensures sqrt x == y)

(*| `sqrt 0.0R == 0.0R`. *)
val sqrt_zero ()
  : Lemma (sqrt 0.0R == 0.0R)

(*| `sqrt 1.0R == 1.0R`. *)
val sqrt_one ()
  : Lemma (sqrt 1.0R == 1.0R)

(*| The square root of the square of a nonnegative real is that real:
    `sqrt (x *. x) == x`. *)
val sqrt_sq (x : rnonneg)
  : Lemma (ensures sqrt (x *. x) == x)

(*| The square root of a positive real is positive.

    Triggered automatically on `sqrt x`. *)
val sqrt_positive (x : rpos)
  : Lemma (ensures sqrt x >. 0.0R)
          [SMTPat (sqrt x)]

(*| `sqrt` is strictly increasing: `x <. y` implies `sqrt x <. sqrt y`. *)
val sqrt_mono (x y : rnonneg)
  : Lemma (requires x <. y) (ensures sqrt x <. sqrt y)

(*| `sqrt` distributes over products: `sqrt (x *. y) == sqrt x *. sqrt y`. *)
val sqrt_mul (x y : rnonneg)
  : Lemma (ensures sqrt (x *. y) == sqrt x *. sqrt y)

(*| `sqrt` distributes over quotients by a positive real:
    `sqrt (x /. y) == sqrt x /. sqrt y`. *)
val sqrt_div (x : rnonneg) (y : rpos)
  : Lemma (ensures sqrt (x /. y) == sqrt x /. sqrt y)

(*| The inverse square root `1.0R /. sqrt x` of a positive real. *)
let rsqrt (x : rpos) : rpos =
  1.0R /. sqrt x
