module FStar.Math.Exp

open FStar.Real

(*| The real exponential function.

    An assumed, uninterpreted function on `FStar.Real.real`: its properties are
    the lemmas of this module, several of which are assumed rather than proved.
    These assumptions do not single out the base e. Reals are erased, so `exp`
    is for specifications and proofs only. *)
val exp (x:real) : real

(*| The logarithm of a positive real: the inverse of `FStar.Math.Exp.exp`.

    See `FStar.Math.Exp.log_exp` and `FStar.Math.Exp.exp_log`. *)
val log (x:real{x >. 0.0R}) : real

(* Usual math laws about exponentiation and logarithms. *)

(*| `exp x` is strictly positive.

    Triggered automatically on `exp x`. *)
val exp_positive (x : real)
  : Lemma (ensures exp x >. 0.0R)
          [SMTPat (exp x)]

(*| `exp 0.0R == 1.0R`.

    Assumed, not proved. *)
val exp_base ()
  : Lemma (exp 0.0R == 1.0R)

(*| `exp` turns sums into products: `exp (x +. y) == exp x *. exp y`.

    Assumed, not proved. Triggered automatically on `exp (x +. y)`. *)
val exp_add (x y : real)
  : Lemma (ensures exp (x +. y) == exp x *. exp y)
          [SMTPat (exp (x +. y))]

(*| `log` undoes `exp`: `log (exp x) == x`.

    Triggered automatically on `log (exp x)`. *)
val log_exp (x : real)
  : Lemma (ensures log (exp x) == x)
          [SMTPat (log (exp x))]

(*| `exp` undoes `log` on positive reals: `exp (log x) == x`.

    Triggered automatically on `exp (log x)`. *)
val exp_log (x : real{x >. 0.0R})
  : Lemma (ensures exp (log x) == x)
          [SMTPat (exp (log x))]

(*| `exp` turns differences into quotients: `exp (x -. y) == exp x /. exp y`.

    Triggered automatically on `exp (x -. y)`. *)
val exp_sub (x y : real)
  : Lemma (ensures exp (x -. y) == exp x /. exp y)
          [SMTPat (exp (x -. y))]

(*| `log` turns products of positive reals into sums:
    `log (x *. y) == log x +. log y`.

    Triggered automatically on `log (x *. y)`. *)
val log_mul (x y : real{x >. 0.0R /\ y >. 0.0R})
  : Lemma (ensures log (x *. y) == log x +. log y)
          [SMTPat (log (x *. y))]

(*| `log` turns quotients of positive reals into differences:
    `log (x /. y) == log x -. log y`.

    Triggered automatically on `log (x /. y)`. *)
val log_div (x y : real{x >. 0.0R /\ y >. 0.0R})
  : Lemma (ensures log (x /. y) == log x -. log y)
          [SMTPat (log (x /. y))]
