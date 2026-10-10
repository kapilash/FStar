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
module FStar.Math.Lib


(*| A natural number is recovered from its quotient and remainder:
    `a = b * (a / b) + a % b`.

    See `FStar.Math.Lemmas.lemma_div_mod` for the version on all integers. *)
val lemma_div_def: a:nat -> b:pos -> Lemma (a = b * (a/b) + a % b)
let lemma_div_def a b = ()

private let mul_lemma (a:nat) (b:nat) (c:nat) : Lemma (requires (a <= b))
                                           (ensures  (c * a <= c * b))
  = ()

private let mul_lemma' (a:nat) (b:nat) (c:pos) : Lemma (requires (c * a <= c * b))
                                           (ensures (a <= b))
  = ()

private let mul_div_lemma (a:nat) (b:pos) : Lemma (b * (a / b) <= a) = ()

(*| Dividing a natural number by a positive integer does not increase it:
    `a / b <= a`.

    Despite its name this is a proved lemma, not an axiom. *)
val slash_decr_axiom: a:nat -> b:pos -> Lemma (a / b <= a)
let slash_decr_axiom a b =
    mul_lemma 1 b a;
    mul_div_lemma a b;
    mul_lemma' (a / b) a b

private let lemma_mul_minus_distr_l (a:int) (b:int) (c:int) : Lemma (a * (b - c) = a * b - a * c)
  = ()

#reset-options
(*| If `a * b = c` then `a = c / b`: exact division undoes multiplication.

    Despite its name this is a proved lemma, not an axiom. See also
    `FStar.Math.Lemmas.cancel_mul_div`. *)
val slash_star_axiom: a:nat -> b:pos -> c:nat -> Lemma
  (requires (a * b = c))
  (ensures  (a = c / b))
let slash_star_axiom a b c =
  lemma_div_def c b;
  lemma_mul_minus_distr_l b a (c/b)

#reset-options
(*| The base-2 logarithm of a positive integer, rounded down.

    `log_2 1` is `0`. *)
val log_2: x:pos -> Tot nat
let rec log_2 x =
  if x >= 2 then 1 + log_2 (x / 2) else 0

(*| Integer power `x` to the `n`, by repeated multiplication; `powx x 0` is `1`.

    See `FStar.Math.Lib.powx_lemma2` for the law of exponents. *)
val powx : x:int -> n:nat -> Tot int
let rec powx x n =
  match n with
  | 0 -> 1
  | n -> x * powx x (n - 1)

(*| The absolute value of an integer. *)
val abs: x:int -> Tot (y:int{ (x >= 0 ==> y = x) /\ (x < 0 ==> y = -x) })
let abs x = if x >= 0 then x else -x

(*| The larger of two integers. *)
val max: x:int -> y:int -> Tot (z:int{ (x >= y ==> z = x) /\ (x < y ==> z = y) })
let max x y = if x >= y then x else y

(*| The smaller of two integers. *)
val min: x:int -> y:int -> Tot (z:int{ (x >= y ==> z = y) /\ (x < y ==> z = x) })
let min x y = if x >= y then y else x

(*| Euclidean (floor) division by a positive integer, whose remainder is
    always nonnegative.

    It computes the same value as the built-in `a / b`; the refinement only
    records that the quotient has the sign of `a`. Contrast with
    `FStar.Math.Lib.div_non_eucl`, which rounds toward zero. *)
val div: a:int -> b:pos -> Tot (c:int{(a < 0 ==> c < 0) /\ (a >= 0 ==> c >= 0)})
let div a b =
  if a < 0 then
    begin
    slash_decr_axiom (-a) b;
    if a % b = 0 then - (-a / b)
    else - (-a / b) - 1
    end
  else a / b

(*| Division rounding toward zero, as the `/` operator of C: the remainder has
    the sign of the dividend.

    Contrast with `FStar.Math.Lib.div` and the built-in `/`, which round down. *)
val div_non_eucl: a:int -> b:pos ->
  Tot (q:int{ ( a >= 0 ==> q = a / b ) /\ ( a < 0 ==> q = -((-a)/b) ) })
let div_non_eucl a b =
  if a < 0 then 0 - ((0 - a) / b)
  else a / b

(*| The mathematical counterpart of the C `<<` operator: `v * pow2 i`, without
    overflow. *)
val shift_left: v:int -> i:nat -> Tot (res:int{res = v * (pow2 i)})
let shift_left v i =
  v * (pow2 i)

(*| Arithmetic shift right, like OCaml `asr`: `v` divided by `pow2 i`, rounding
    down, so negative values stay negative. *)
val arithmetic_shift_right: v:int -> i:nat -> Tot (res:int{ res = div v (pow2 i) })
let arithmetic_shift_right v i = 
  div v (pow2 i)

(* Case of C cast functions ? *)
(*| Remainder of division rounding toward zero, as `%` in C or `mod` in OCaml:
    the result has the sign of `v`.

    It satisfies `v = div_non_eucl v p * p + signed_modulo v p`; see
    `FStar.Math.Lib.div_non_eucl` and `FStar.Math.Lib.signed_modulo_property`. *)
val signed_modulo: v:int -> p:pos -> Tot (res:int{ res = v - ((div_non_eucl v p) * p) })
let signed_modulo v p =
  if v >= 0 then v % p
  else 0 - ( (0-v) % p)

(*| Infix notation for `FStar.Math.Lib.signed_modulo`: `a +% p` is the
    remainder of `a` rounded toward zero, with the sign of `a`. *)
val ( +% ) : a:int -> p:pos -> 
  Tot (res:int{ (a >= 0 ==> res = a % p) /\ (a < 0 ==> res = -((-a) % p)) }) 
let ( +% ) a p = signed_modulo a p

(** Useful lemmas for future proofs **)

(* Lemmas of x^n *)
(*| Any integer to the power `1` is itself. *)
val powx_lemma1: a:int -> Lemma (powx a 1 = a)
let powx_lemma1 a = ()

(*| Powers multiply by adding exponents:
    `powx x n * powx x m = powx x (n + m)`. *)
val powx_lemma2: x:int -> n:nat -> m:nat -> Lemma
  (powx x n * powx x m = powx x (n + m))
let rec powx_lemma2 x n m =
  let ass (x y z : int) : Lemma ((x*y)*z == x*(y*z)) = () in
  match n with
  | 0 -> ()
  | _ -> powx_lemma2 x (n-1) m; ass x (powx x (n-1)) (powx x m)

(*| The absolute value of a product is the product of the absolute values.

    See also `FStar.Math.Lemmas.lemma_abs_mul`. *)
val abs_mul_lemma: a:int -> b:int -> Lemma (abs (a * b) = abs a * abs b)
let abs_mul_lemma a b = ()

(*| The result of `FStar.Math.Lib.signed_modulo v p` is below `p` in absolute
    value. *)
val signed_modulo_property: v:int -> p:pos -> Lemma (abs (signed_modulo v p ) < p)
let signed_modulo_property v p = ()

(*| Division rounding toward zero does not increase the absolute value. *)
val div_non_eucl_decr_lemma: a:int -> b:pos -> Lemma (abs (div_non_eucl a b) <= abs a)
let div_non_eucl_decr_lemma a b =
  slash_decr_axiom (abs a) b

(*| Division rounding toward zero gives `0` when the divisor exceeds the
    absolute value of the dividend. *)
val div_non_eucl_bigger_denom_lemma: a:int -> b:pos -> Lemma
  (requires (b > abs a))
  (ensures  (div_non_eucl a b = 0))
let div_non_eucl_bigger_denom_lemma a b = ()
