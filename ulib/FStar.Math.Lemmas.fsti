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
module FStar.Math.Lemmas


(*| Euclidean division leaves a remainder `a - b * (a / b)` in the range from
    `0` (inclusive) to `b` (exclusive).

    Despite its name this is a proved lemma, not an axiom. See also
    `FStar.Math.Lemmas.lemma_div_mod` and `FStar.Math.Lemmas.lemma_mod_lt`. *)
val euclidean_div_axiom: a:int -> b:pos -> Lemma
  (a - b * (a / b) >= 0 /\ a - b * (a / b) < b)

(*| If `a < q` then `a + q * b < q * (b + 1)`.

    Typically used with `a` a remainder modulo `q` and `b` a quotient, to bound
    a value rebuilt from its quotient and remainder. *)
val lemma_eucl_div_bound: a:int -> b:int -> q:int -> Lemma
  (requires (a < q))
  (ensures  (a + q * b < q * (b+1)))

(*| Multiplying both sides of `b <= c` on the left by a natural number `a`
    preserves the order: `a * b <= a * c`. *)
val lemma_mult_le_left: a:nat -> b:int -> c:int -> Lemma
  (requires (b <= c))
  (ensures  (a * b <= a * c))

(*| Multiplying both sides of `b <= c` on the right by a natural number `a`
    preserves the order: `b * a <= c * a`. *)
val lemma_mult_le_right: a:nat -> b:int -> c:int -> Lemma
  (requires (b <= c))
  (ensures  (b * a <= c * a))

(*| Multiplying both sides of `b < c` on the left by a positive `a` preserves
    the strict order: `a * b < a * c`. *)
val lemma_mult_lt_left: a:pos -> b:int -> c:int -> Lemma
  (requires (b < c))
  (ensures  (a * b < a * c))

(*| Multiplying both sides of `b < c` on the right by a positive `a` preserves
    the strict order: `b * a < c * a`. *)
val lemma_mult_lt_right: a:pos -> b:int -> c:int -> Lemma
  (requires (b < c))
  (ensures  (b * a < c * a))

(*| The product of two natural numbers below `k` is below `k * k`. *)
val lemma_mult_lt_sqr (n:nat) (m:nat) (k:nat{n < k && m < k})
  : Lemma (n * m < k * k)

(*| Multiplication on integers is commutative: `a * b = b * a`. *)
val swap_mul: a:int -> b:int -> Lemma (a * b = b * a)

(*| A positive factor can be cancelled from both sides of an equation: from
    `a * n = b * n` conclude `a = b`. *)
val lemma_cancel_mul (a b : int) (n : pos) : Lemma (requires (a * n = b * n)) (ensures (a = b))

(*| Multiplication distributes over addition on the right:
    `(a + b) * c = a * c + b * c`. *)
val distributivity_add_left: a:int -> b:int -> c:int -> Lemma
  ((a + b) * c = a * c + b * c)

(*| Multiplication distributes over addition on the left:
    `a * (b + c) = a * b + a * c`. *)
val distributivity_add_right: a:int -> b:int -> c:int -> Lemma
  (a * (b + c) = a * b + a * c)

(* GM: This is really just an identity since the LHS is associated to the left *)
(*| States `a * b * c = (a * b) * c`.

    This is a syntactic identity, since `*` associates to the left; it is kept
    for symmetry with `FStar.Math.Lemmas.paren_mul_right`. *)
val paren_mul_left: a:int -> b:int -> c:int -> Lemma
  (a * b * c = (a * b) * c)

(*| Multiplication is associative: `a * b * c = a * (b * c)`.

    Useful to regroup nonlinear products that Z3 does not reassociate on its
    own. *)
val paren_mul_right: a:int -> b:int -> c:int -> Lemma
  (a * b * c = a * (b * c))

(*| States `a + b + c = (a + b) + c`, a syntactic identity since `+`
    associates to the left. *)
val paren_add_left: a:int -> b:int -> c:int -> Lemma
  (a + b + c = (a + b) + c)

(*| Addition is associative: `a + b + c = a + (b + c)`. *)
val paren_add_right: a:int -> b:int -> c:int -> Lemma
  (a + b + c = a + (b + c))

(*| Addition is associative, in both groupings of `a + b + c`.

    Combines `FStar.Math.Lemmas.paren_add_left` and
    `FStar.Math.Lemmas.paren_add_right`. *)
val addition_is_associative: a:int -> b:int -> c:int -> Lemma
  (a + b + c = (a + b) + c /\ a + b + c = a + (b + c))

(*| Regrouping rules for sums and differences of three integers, such as
    `a - b - c = a - (b + c)` and `a - (b - c) = a - b + c`. *)
val subtraction_is_distributive: a:int -> b:int -> c:int -> Lemma
  (a - b + c = (a - b) + c /\
   a - b - c = a - (b + c) /\
   a - b - c = (a - b) - c /\
   a + (-b - c) = a - b - c /\
   a - (b - c) = a - b + c)

(*| Reorders a sum and a difference: `a + b - c = (a - c) + b`. *)
val swap_add_plus_minus: a:int -> b:int -> c:int -> Lemma
  (a + b - c = (a - c) + b)

(*| Negation of a product moves to the left factor: `-(a * b) = (-a) * b`. *)
val neg_mul_left: a:int -> b:int -> Lemma (-(a * b) = (-a) * b)

(*| Negation of a product moves to the right factor: `-(a * b) = a * (-b)`. *)
val neg_mul_right: a:int -> b:int -> Lemma (-(a * b) = a * (-b))

(*| Negation can move between the factors of a product: `(-a) * b = a * (-b)`. *)
val swap_neg_mul: a:int -> b:int -> Lemma ((-a) * b = a * (-b))

(*| Multiplication distributes over subtraction on the right:
    `(a - b) * c = a * c - b * c`. *)
val distributivity_sub_left: a:int -> b:int -> c:int ->
  Lemma ((a - b) * c = a * c - b * c)

(*| Multiplication distributes over subtraction on the left:
    `a * (b - c) = a * b - a * c`. *)
val distributivity_sub_right: a:int -> b:int -> c:int ->
  Lemma ((a * (b - c) = a * b - a * c))

(*| States `a + (b * c) = a + b * c`, a syntactic identity since `*` binds
    tighter than `+`. *)
val mul_binds_tighter: a:int -> b:int -> c:int -> Lemma (a + (b * c) = a + b * c)

(*| The absolute value of a product is the product of the absolute values:
    `abs a * abs b = abs (a * b)`. *)
val lemma_abs_mul : a:int -> b:int -> Lemma (abs a * abs b = abs (a * b))

(*| `abs a < b` holds exactly when `-b < a` and `a < b`. *)
val lemma_abs_bound : a:int -> b:nat -> Lemma (abs a < b <==> -b < a /\ a < b)

(*| Symmetric bounds multiply: if `-b < a < b` and `-d < c < d` then
    `-(b * d) < a * c < b * d`. *)
val mul_ineq1: a:int -> b:nat -> c:int -> d:nat -> Lemma
    (requires (-b < a /\ a < b /\
               -d < c /\ c < d))
    (ensures  (-(b * d) < a * c /\ a * c < b * d))

(*| Zero is a left identity for addition: `0 + n = n`. *)
val add_zero_left_is_same (n : int) : Lemma(0 + n = n)
(*| Zero is a right identity for addition: `n + 0 = n`. *)
val add_zero_right_is_same (n : int) : Lemma(n + 0 = n)

(*| One is a left identity for multiplication: `1 * n = n`. *)
val mul_one_left_is_same (n : int) : Lemma(1 * n = n)
(*| One is a right identity for multiplication: `n * 1 = n`. *)
val mul_one_right_is_same (n : int) : Lemma(n * 1 = n)

(*| Zero is absorbing on the left of a product: `0 * n = 0`. *)
val mul_zero_left_is_zero (n : int) : Lemma(0 * n = 0)
(*| Zero is absorbing on the right of a product: `n * 0 = 0`. *)
val mul_zero_right_is_zero (n : int) : Lemma(n * 0 = 0)

(*| The product of two natural numbers is nonnegative.

    See also `FStar.Math.Lemmas.lemma_mul_nat_pos_is_nat`. *)
val nat_times_nat_is_nat: a:nat -> b:nat -> Lemma (a * b >= 0)

(*| The product of two positive integers is positive.

    Same as `FStar.Math.Lemmas.lemma_mul_pos_pos_is_pos`. *)
val pos_times_pos_is_pos: a:pos -> b:pos -> Lemma (a * b > 0)

(*| Dividing a natural number by a positive integer gives a nonnegative
    quotient. *)
val nat_over_pos_is_nat: a:nat -> b:pos -> Lemma (a / b >= 0)

(*| If the sum of two natural numbers is `0`, both are `0`. *)
val nat_plus_nat_equal_zero_lemma: a:nat -> b:nat{a + b = 0} -> Lemma(a = 0 /\ b = 0)

(*| If a product of two integers is `0`, one of the factors is `0`. *)
val int_times_int_equal_zero_lemma: a:int -> b:int{a * b = 0} -> Lemma(a = 0 \/ b = 0)

(*| Doubling a power of two by addition: `pow2 n + pow2 n = pow2 (n + 1)`. *)
val pow2_double_sum: n:nat -> Lemma (pow2 n + pow2 n = pow2 (n + 1))

(*| Doubling a power of two by multiplication: `2 * pow2 n = pow2 (n + 1)`. *)
val pow2_double_mult: n:nat -> Lemma (2 * pow2 n = pow2 (n + 1))

(*| `pow2` is strictly increasing: `m < n` implies `pow2 m < pow2 n`. *)
val pow2_lt_compat: n:nat -> m:nat -> Lemma
  (requires (m < n))
  (ensures  (pow2 m < pow2 n))
  (decreases m)

(*| `pow2` is monotone: `m <= n` implies `pow2 m <= pow2 n`. *)
val pow2_le_compat: n:nat -> m:nat -> Lemma
  (requires (m <= n))
  (ensures  (pow2 m <= pow2 n))

(*| Powers of two multiply by adding exponents:
    `pow2 n * pow2 m = pow2 (n + m)`. *)
val pow2_plus: n:nat -> m:nat -> Lemma
  (ensures (pow2 n * pow2 m = pow2 (n + m)))
  (decreases n)

(*| Dividing powers of two subtracts exponents: when `m <= n`,
    `pow2 n / pow2 m = pow2 (n - m)`. *)
val pow2_minus: n:nat -> m:nat{ n >= m } -> Lemma
  ((pow2 n) / (pow2 m) = pow2 (n - m))

(*| Division rounds down for a positive divisor: `n * (a / n) <= a`.

    The divisor `n` may be any nonzero integer; for a negative `n` the
    inequality also holds because `/` is Euclidean division. *)
val multiply_fractions (a:int) (n:nonzero) : Lemma (n * ( a / n ) <= a)

(*| A natural number below the modulus is its own remainder: if `a < b` then
    `a % b = a`.

    Same as `FStar.Math.Lemmas.small_mod`. *)
val modulo_lemma: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a))

(*| An integer is recovered from its quotient and remainder:
    `a = p * (a / p) + a % p`.

    Same as `FStar.Math.Lib.lemma_div_def`, but for any integer `a` and any
    nonzero `p`. See also `FStar.Math.Lemmas.euclidean_division_definition`. *)
val lemma_div_mod: a:int -> p:nonzero -> Lemma (a = p * (a / p) + a % p)

(*| The remainder `a % p` lies between `0` (inclusive) and `p` (exclusive), and
    is at most `a` when `a` is nonnegative. *)
val lemma_mod_lt: a:int -> p:pos -> Lemma (0 <= a % p /\ a % p < p /\ (a >= 0 ==> a % p <= a))

(*| Dividing a value below `pow2 n` by `pow2 m`, with `m <= n`, gives a value
    below `pow2 (n - m)`.

    `FStar.Math.Lemmas.lemma_div_lt` is the same with `m <= n` as a
    precondition rather than a refinement. *)
val lemma_div_lt_nat: a:int -> n:nat -> m:nat{m <= n} ->
  Lemma (requires (a < pow2 n))
        (ensures  (a / pow2 m < pow2 (n-m)))

(*| Dividing a value below `pow2 n` by `pow2 m`, with `m <= n`, gives a value
    below `pow2 (n - m)`.

    A variant of `FStar.Math.Lemmas.lemma_div_lt_nat`. *)
val lemma_div_lt (a:int) (n:nat) (m:nat) : Lemma
  (requires m <= n /\ a < pow2 n)
  (ensures a / pow2 m < pow2 (n-m))

(*| The only multiple `x * n` of a positive `n` strictly between `-n` and `n`
    is `0`, so `x == 0`. *)
val bounded_multiple_is_zero (x:int) (n:pos) : Lemma
  (requires -n < x * n /\ x * n < n)
  (ensures x == 0)

(*| A natural number below the divisor has quotient `0`: if `a < n` then
    `a / n == 0`. *)
val small_div (a:nat) (n:pos) : Lemma (requires a < n) (ensures a / n == 0)

(*| A natural number below the modulus is its own remainder: if `a < n` then
    `a % n == a`. *)
val small_mod (a:nat) (n:pos) : Lemma (requires a < n) (ensures a % n == a)

(*| Two natural numbers below `n` that differ by a multiple `x * n` of `n` are
    equal, and `x == 0`. *)
val lt_multiple_is_equal (a:nat) (b:nat) (x:int) (n:nonzero) : Lemma
  (requires a < n /\ b < n /\ a == b + x * n)
  (ensures a == b /\ x == 0)

(*| Adding a multiple of the modulus does not change the remainder:
    `(a + k * n) % n = a % n`. *)
val lemma_mod_plus (a:int) (k:int) (n:pos) : Lemma ((a + k * n) % n = a % n)

(*| Adding `k` times the divisor adds `k` to the quotient:
    `(a + k * n) / n = a / n + k`. *)
val lemma_div_plus (a:int) (k:int) (n:pos) : Lemma ((a + k * n) / n = a / n + k)

(*| Adding `k * n` adds `k` to the quotient by `n` and leaves the remainder
    modulo `n` unchanged.

    Combines `FStar.Math.Lemmas.lemma_div_plus` and
    `FStar.Math.Lemmas.lemma_mod_plus`. *)
val lemma_div_mod_plus (a:int) (k:int) (n:pos)
  : Lemma ((a + k * n) / n = a / n + k /\
           (a + k * n) % n = a % n)

(*| Adding `n` once leaves `a % n` unchanged and increments `a / n`. *)
val add_div_mod_1 (a:int) (n:pos)
  : Lemma ((a + n) % n == a % n /\
           (a + n) / n == a / n + 1)

(*| Subtracting `n` once leaves `a % n` unchanged and decrements `a / n`. *)
val sub_div_mod_1 (a:int) (n:pos)
  : Lemma ((a - n) % n == a % n /\
           (a - n) / n == a / n - 1)

(*| Multiplying by a nonzero `n` and then dividing by `n` is the identity:
    `(a * n) / n == a`. *)
val cancel_mul_div (a:int) (n:nonzero) : Lemma ((a * n) / n == a)

(*| A multiple of `n` has remainder `0`: `(a * n) % n == 0`. *)
val cancel_mul_mod (a:int) (n:pos) : Lemma ((a * n) % n == 0)

(*| The second summand may be reduced first: `(a + b % n) % n = (a + b) % n`.

    See also `FStar.Math.Lemmas.lemma_mod_plus_distr_l` and
    `FStar.Math.Lemmas.modulo_distributivity`. *)
val lemma_mod_add_distr (a:int) (b:int) (n:pos) : Lemma ((a + b % n) % n = (a + b) % n)

(*| The subtrahend may be reduced first: `(a - b % n) % n = (a - b) % n`. *)
val lemma_mod_sub_distr (a:int) (b:int) (n:pos) : Lemma ((a - b % n) % n = (a - b) % n)

(*| Minus one modulo a positive `a` is `a - 1`. *)
val lemma_mod_sub_0: a:pos -> Lemma ((-1) % a = a - 1)

(*| For `0 < a < b`, `(-a) % b = b - (a % b)`. *)
val lemma_mod_sub_1: a:pos -> b:pos{a < b} -> Lemma ((-a) % b = b - (a%b))

(*| The left factor may be reduced first: `(a * b) % n = ((a % n) * b) % n`.

    Together with `FStar.Math.Lemmas.lemma_mod_mul_distr_r` this reduces both
    factors of a product modulo `n`:

    ```fstar
    let mod_of_product (a b: int) (n: pos)
      : Lemma ((a % n) * (b % n) % n == (a * b) % n)
      = FStar.Math.Lemmas.lemma_mod_mul_distr_l a b n;
        FStar.Math.Lemmas.lemma_mod_mul_distr_r (a % n) b n
    ``` *)
val lemma_mod_mul_distr_l (a:int) (b:int) (n:pos) : Lemma
  (requires True)
  (ensures (a * b) % n = ((a % n) * b) % n)


(*| The right factor may be reduced first: `(a * b) % n = (a * (b % n)) % n`.

    See `FStar.Math.Lemmas.lemma_mod_mul_distr_l` for the left factor. *)
val lemma_mod_mul_distr_r (a:int) (b:int) (n:pos) : Lemma ((a * b) % n = (a * (b % n)) % n)

(*| Two natural numbers below `p` with the same remainder modulo `p` are equal. *)
val lemma_mod_injective: p:pos -> a:nat -> b:nat -> Lemma
  (requires (a < p /\ b < p /\ a % p = b % p))
  (ensures  (a = b))

(*| Factors a common left factor out of a difference:
    `a * b - a * c = a * (b - c)`. *)
val lemma_mul_sub_distr: a:int -> b:int -> c:int -> Lemma
  (a * b - a * c = a * (b - c))

(*| When `p` divides `a` exactly (`a % p = 0`), `a = p * (a / p)`.

    See also `FStar.Math.Lemmas.div_exact_r` for the factors in the other
    order. *)
val lemma_div_exact: a:int -> p:pos -> Lemma
  (requires (a % p = 0))
  (ensures  (a = p * (a / p)))

(*| When `n` divides `a` exactly (`a % n = 0`), `a = (a / n) * n`. *)
val div_exact_r (a:int) (n:pos) : Lemma
  (requires (a % n = 0))
  (ensures  (a = (a / n) * n))

(*| Removing the remainder does not change the quotient:
    `a / p = (a - a % p) / p`. *)
val lemma_mod_spec: a:int -> p:pos -> Lemma
  (a / p = (a - (a % p)) / p)

(*| An integer is its remainder plus `q * p`, where `q = (a - a % p) / p`. *)
val lemma_mod_spec2: a:int -> p:pos -> Lemma
  (let q:int = (a - (a % p)) / p in a = (a % p) + q * p)

(*| The first summand may be reduced first:
    `(a + b) % p = ((a % p) + b) % p`. *)
val lemma_mod_plus_distr_l: a:int -> b:int -> p:pos -> Lemma
  ((a + b) % p = ((a % p) + b) % p)

(*| The second summand may be reduced first:
    `(a + b) % p = (a + (b % p)) % p`. *)
val lemma_mod_plus_distr_r: a:int -> b:int -> p:pos -> Lemma
  ((a + b) % p = (a + (b % p)) % p)

(*| If `a = b % p` then `a % p = b % p`; reducing twice is the same as reducing
    once.

    See also `FStar.Math.Lemmas.lemma_mod_twice`. *)
val lemma_mod_mod: a:int -> b:int -> p:pos -> Lemma
  (requires (a = b % p))
  (ensures  (a % p = b % p))

(* * Lemmas about multiplication, division and modulo. **)
(* * This part focuses on the situation where          **)
(* * dividend: nat    divisor: pos                     **)
(* * TODO: add triggers for certain lemmas.            **)

(*| An integer is recovered from its quotient and remainder by a nonzero
    divisor: `a = (a / b) * b + a % b`.

    See also `FStar.Math.Lemmas.lemma_div_mod`. *)
val euclidean_division_definition: a:int -> b:nonzero ->
  Lemma (a = (a / b) * b + a % b)

(*| The remainder `a % b` by a positive `b` is at least `0` and below `b`. *)
val modulo_range_lemma: a:int -> b:pos ->
  Lemma (a % b >= 0 && a % b < b)

(*| A natural number below the modulus is its own remainder: if `a < b` then
    `a % b = a`.

    Same as `FStar.Math.Lemmas.small_mod`, for any nonzero `b`. *)
val small_modulo_lemma_1: a:nat -> b:nonzero ->
  Lemma (requires a < b) (ensures a % b = a)

(*| If `a % b = a` then `a < b`: an integer that is its own remainder is below
    the modulus. *)
val small_modulo_lemma_2: a:int -> b:pos ->
  Lemma (requires a % b = a) (ensures a < b)

(*| A natural number below the divisor has quotient `0`: if `a < b` then
    `a / b = 0`.

    Same as `FStar.Math.Lemmas.small_div`, for any nonzero `b`. *)
val small_division_lemma_1: a:nat -> b:nonzero ->
  Lemma (requires a < b) (ensures a / b = 0)

(*| If `a / n = 0` then `a` is between `0` (inclusive) and `n` (exclusive).

    The converse of `FStar.Math.Lemmas.small_div`. *)
val small_division_lemma_2 (a:int) (n:pos) : Lemma
  (requires a / n = 0)
  (ensures 0 <= a /\ a < n)

(*| Multiplying by a positive `p` preserves and reflects order:
    `a >= b` holds exactly when `a * p >= b * p`. *)
val multiplication_order_lemma: a:int -> b:int -> p:pos ->
  Lemma (a >= b <==> a * p >= b * p)

(*| The quotient times the divisor lies just below the dividend:
    `a - b < (a / b) * b` and `(a / b) * b <= a`. *)
val division_propriety: a:int -> b:pos ->
  Lemma (a - b < (a / b) * b && (a / b) * b <= a)

(*| If `a - b < m * b` then `m > a / b - 1`.

    A step in the proof of `FStar.Math.Lemmas.division_definition`; prefer
    that lemma. *)
val division_definition_lemma_1: a:int -> b:pos -> m:int{a - b < m * b} ->
  Lemma (m > a / b - 1)

(*| If `m * b <= a` then `m < a / b + 1`.

    A step in the proof of `FStar.Math.Lemmas.division_definition`; prefer
    that lemma. *)
val division_definition_lemma_2: a:int -> b:pos -> m:int{m * b <= a} ->
  Lemma (m < a / b + 1)

(*| Characterizes the quotient: if `a - b < m * b` and `m * b <= a` then
    `m = a / b`.

    Use it to show that a candidate value is the quotient. *)
val division_definition: a:int -> b:pos -> m:int{a - b < m * b && m * b <= a} ->
  Lemma (m = a / b)

(*| Multiplying by a nonzero `n` and then dividing by `n` is the identity:
    `(a * n) / n = a`.

    Identical to `FStar.Math.Lemmas.cancel_mul_div`. *)
val multiple_division_lemma (a:int) (n:nonzero) : Lemma ((a * n) / n = a)

(*| A multiple of `n` has remainder `0`: `(a * n) % n = 0`.

    Identical to `FStar.Math.Lemmas.cancel_mul_mod`. *)
val multiple_modulo_lemma (a:int) (n:pos) : Lemma ((a * n) % n = 0)

(*| Adding `n` times the divisor adds `n` to the quotient:
    `(a + n * b) / b = a / b + n`.

    See also `FStar.Math.Lemmas.lemma_div_plus`. *)
val division_addition_lemma: a:int -> b:pos -> n:int ->
  Lemma ( (a + n * b) / b = a / b + n )

(*| Remainders of a sum can be computed from the remainders of the summands:
    `(a + b) % c == (a % c + b % c) % c`.

    ```fstar
    let mod_of_sum (a b: int) (n: pos)
      : Lemma ((a % n + b % n) % n == (a + b) % n)
      = FStar.Math.Lemmas.modulo_distributivity a b n
    ``` *)
val modulo_distributivity: a:int -> b:int -> c:pos -> Lemma ((a + b) % c == (a % c + b % c) % c)

(*| Division by a positive `d` is monotone: `a <= b` implies `a / d <= b / d`. *)
val lemma_div_le: a:int -> b:int -> d:pos ->
  Lemma (requires (a <= b))
        (ensures  (a / d <= b / d))

(*| Subtracting `b` times the divisor subtracts `b` from the quotient:
    `(a - b * n) / n = a / n - b`. *)
val division_sub_lemma (a:int) (n:pos) (b:nat) : Lemma ((a - b * n) / n = a / n - b)

(*| Reduces every operand of `(a + b) * c` modulo `p` before computing the
    remainder of the whole expression. *)
val lemma_mod_plus_mul_distr: a:int -> b:int -> c:int -> p:pos -> Lemma
  (((a + b) * c) % p = ((((a % p) + (b % p)) % p) * (c % p)) % p)

(*| Adding a multiple of the modulus does not change the remainder:
    `(a + b * n) % n = a % n`.

    See also `FStar.Math.Lemmas.lemma_mod_plus`. *)
val modulo_addition_lemma (a:int) (n:pos) (b:int) : Lemma ((a + b * n) % n = a % n)

(*| Subtracting a multiple of the modulus does not change the remainder:
    `(a - b * n) % n = a % n`. *)
val lemma_mod_sub (a:int) (n:pos) (b:int) : Lemma (ensures (a - b * n) % n = a % n)

(*| If `n * q` divides `a` then `n` divides `a`: `a % (n * q) == 0` implies
    `a % n == 0`. *)
val mod_mult_exact (a:int) (n:pos) (q:pos) : Lemma
  (requires (a % (n * q) == 0))
  (ensures a % n == 0)

(*| If `b * n` divides `a` then `n` divides `a / b`. *)
val mod_mul_div_exact (a:int) (b:pos) (n:pos) : Lemma
  (requires (a % (b * n) == 0))
  (ensures (a / b) % n == 0)

(*| If `pow2 m` divides `a` (with `m > 0`) then `pow2 (m - 1)` divides `a / 2`. *)
val mod_pow2_div2 (a:int) (m:pos) : Lemma
  (requires a % pow2 m == 0)
  (ensures (a / 2) % pow2 (m - 1) == 0)

(*| Dividing by a product is dividing by each factor in turn:
    `a / (b * c) = (a / b) / c`. *)
val division_multiplication_lemma (a:int) (b:pos) (c:pos) : Lemma
  (a / (b * c) = (a / b) / c)

(*| Scaling both the value and the modulus by `b` scales the remainder:
    `(a * b) % (b * c) == (a % c) * b`. *)
val modulo_scale_lemma : a:int -> b:pos -> c:pos -> Lemma ((a * b) % (b * c) == (a % c) * b)

(*| The product of two positive integers is positive.

    Same as `FStar.Math.Lemmas.pos_times_pos_is_pos`. *)
val lemma_mul_pos_pos_is_pos (x:pos) (y:pos) : Lemma (x*y > 0)
(*| The product of a natural number and a positive integer is nonnegative. *)
val lemma_mul_nat_pos_is_nat (x:nat) (y:pos) : Lemma (x*y >= 0)

(*| Extracts a middle digit in a mixed radix: `(a % (b * c)) / b = (a / b) % c`.

    See `FStar.Math.Lemmas.pow2_modulo_division_lemma_1` for the
    powers-of-two version. *)
val modulo_division_lemma: a:nat -> b:pos -> c:pos ->
    Lemma ((a % (b * c)) / b = (a / b) % c)

(*| Reducing modulo a multiple `b * c` of `b` and then modulo `b` is the same
    as reducing modulo `b`: `(a % (b * c)) % b = a % b`. *)
val modulo_modulo_lemma (a:int) (b:pos) (c:pos) : Lemma
  ((a % (b * c)) % b = a % b)

(*| Shifting left by `c` and then right by `b`, with `c >= b`, is a shift left
    by `c - b`: `(a * pow2 c) / pow2 b = a * pow2 (c - b)`. *)
val pow2_multiplication_division_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
  Lemma ( (a * pow2 c) / pow2 b = a * pow2 (c - b))

(*| Shifting left by `c` and then right by `b`, with `c <= b`, is a shift right
    by `b - c`: `(a * pow2 c) / pow2 b = a / pow2 (b - c)`. *)
val pow2_multiplication_division_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
  Lemma ( (a * pow2 c) / pow2 b = a / pow2 (b - c))

(*| Shifting left by `c` clears the low `b` bits when `c >= b`:
    `(a * pow2 c) % pow2 b = 0`. *)
val pow2_multiplication_modulo_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
  Lemma ( (a * pow2 c) % pow2 b = 0 )

(*| Keeping the low `b` bits of `a * pow2 c`, with `c <= b`, keeps the low
    `b - c` bits of `a` and shifts them: the result is
    `(a % pow2 (b - c)) * pow2 c`. *)
val pow2_multiplication_modulo_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
  Lemma ( (a * pow2 c) % pow2 b = (a % pow2 (b - c)) * pow2 c )

(*| Extracts bits `b` to `c - 1` of a natural number, with `c >= b`:
    `(a % pow2 c) / pow2 b = (a / pow2 b) % pow2 (c - b)`.

    ```fstar
    let middle_bits (x: nat) (n m: nat)
      : Lemma ((x % pow2 (n + m)) / pow2 n == (x / pow2 n) % pow2 m)
      = FStar.Math.Lemmas.pow2_modulo_division_lemma_1 x n (n + m)
    ``` *)
val pow2_modulo_division_lemma_1: a:nat -> b:nat -> c:nat{c >= b} ->
  Lemma ( (a % pow2 c) / pow2 b = (a / pow2 b) % (pow2 (c - b)) )

(*| The low `c` bits shifted right by at least `c` give `0`: when `c <= b`,
    `(a % pow2 c) / pow2 b = 0`. *)
val pow2_modulo_division_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
  Lemma ( (a % pow2 c) / pow2 b = 0 )

(*| Truncating to `c` bits and then to `b <= c` bits is truncating to `b` bits:
    `(a % pow2 c) % pow2 b = a % pow2 b`. *)
val pow2_modulo_modulo_lemma_1: a:int -> b:nat -> c:nat{c >= b} ->
  Lemma ( (a % pow2 c) % pow2 b = a % pow2 b )

(*| Truncating to `c` bits and then to `b >= c` bits leaves the first result
    unchanged: `(a % pow2 c) % pow2 b = a % pow2 c`. *)
val pow2_modulo_modulo_lemma_2: a:int -> b:nat -> c:nat{c <= b} ->
  Lemma ( (a % pow2 c) % pow2 b = a % pow2 c )

(*| Congruence is preserved by adding the same value on the left: if
    `b % p = c % p` then `(a + b) % p = (a + c) % p`.

    See also `FStar.Math.Lemmas.mod_add_both`. *)
val modulo_add : p:pos -> a:int -> b:int -> c:int -> Lemma
  (requires (b % p = c % p))
  (ensures  ((a + b) % p = (a + c) % p))

(*| Reducing twice is the same as reducing once: `(a % p) % p == a % p`. *)
val lemma_mod_twice : a:int -> p:pos -> Lemma ((a % p) % p == a % p)

(*| A common summand can be cancelled from a congruence: if
    `(a + b) % p = (a + c) % p` then `b % p = c % p`. *)
val modulo_sub : p:pos -> a:int -> b:int -> c:int -> Lemma
  (requires ((a + b) % p = (a + c) % p))
  (ensures (b % p = c % p))

(*| Congruence is preserved by adding the same value on the right: if
    `a % n == b % n` then `(a + x) % n == (b + x) % n`. *)
val mod_add_both (a:int) (b:int) (x:int) (n:pos) : Lemma
  (requires a % n == b % n)
  (ensures (a + x) % n == (b + x) % n)

(*| Adding the same `a` to two natural numbers `b` and `c` below `n` gives
    distinct remainders unless `b = c`. *)
val lemma_mod_plus_injective (n:pos) (a:int) (b:nat) (c:nat) : Lemma
  (requires b < n /\ c < n /\ (a + b) % n = (a + c) % n)
  (ensures  b = c)

(*| Characterizes the remainder: if `0 <= b < c` and `c` divides `a - b`, then
    `b = a % c`. *)
val modulo_sub_lemma (a : int) (b : nat) (c : pos) :
  Lemma
  (requires (b < c /\ (a - b) % c = 0))
  (ensures (b = a % c))