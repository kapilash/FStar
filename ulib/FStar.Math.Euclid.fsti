module FStar.Math.Euclid


///
/// Divides relation
///
/// It is reflexive, transitive, and antisymmetric up to sign.
/// When a <> 0, a `divides` b iff b % a = 0 (this is proved below)
///

(*| `a` divides `b` when `b` is an integer multiple `q * a` of `a`.

    A classical, existentially quantified relation. Every integer divides `0`,
    and `0` divides only `0`. For a nonzero `a` it coincides with `b % a = 0`;
    see `FStar.Math.Euclid.mod_divides` and `FStar.Math.Euclid.divides_mod`. *)
let divides (a b:int) : prop = exists q. b = q * a

(*| Every integer divides itself.

    Triggered automatically on `divides a a`. *)
val divides_reflexive (a:int) : Lemma (a `divides` a) [SMTPat (a `divides` a)]

(*| Divisibility is transitive: if `a` divides `b` and `b` divides `c` then
    `a` divides `c`. *)
val divides_transitive (a b c:int) : Lemma
  (requires a `divides` b /\ b `divides` c)
  (ensures  a `divides` c)

(*| Divisibility is antisymmetric up to sign: if `a` and `b` divide each other
    then `a = b` or `a = -b`. *)
val divide_antisym (a b:int) : Lemma
  (requires a `divides` b /\ b `divides` a)
  (ensures  a = b \/ a = -b)

(*| Every integer divides `0`. *)
val divides_0 (a:int) : Lemma (a `divides` 0)

(*| Only `1` and `-1` divide `1`. *)
val divides_1 (a:int) : Lemma (requires a `divides` 1) (ensures a = 1 \/ a = -1)

(*| If `a` divides `b` then `a` divides `-b`. *)
val divides_minus (a b:int) : Lemma
  (requires a `divides` b)
  (ensures  a `divides` (-b))

(*| If `a` divides `b` then `-a` divides `b`. *)
val divides_opp (a b:int) : Lemma
  (requires a `divides` b)
  (ensures (-a) `divides` b)

(*| A common divisor of `a` and `b` divides `a + b`. *)
val divides_plus (a b d:int) : Lemma
  (requires d `divides` a /\ d `divides` b)
  (ensures  d `divides` (a + b))

(*| A common divisor of `a` and `b` divides `a - b`. *)
val divides_sub (a b d:int) : Lemma
  (requires d `divides` a /\ d `divides` b)
  (ensures  d `divides` (a - b))

(*| If `d` divides `b` then `d` divides any multiple `a * b`. *)
val divides_mult_right (a b d:int) : Lemma
  (requires d `divides` b)
  (ensures  d `divides` (a * b))

///
/// Greatest Common Divisor (GCD) relation
///
/// We deviate from the standard definition in that we allow the divisor to
/// be negative. Thus, the GCD of two integers is unique up to sign.
///

(*| `d` is a greatest common divisor of `a` and `b`: it divides both, and every
    common divisor of `a` and `b` divides `d`.

    Unlike the usual definition, `d` may be negative, so the GCD is unique only
    up to sign (see `FStar.Math.Euclid.is_gcd_unique`). Computed by
    `FStar.Math.Euclid.euclid_gcd`. *)
let is_gcd (a b d:int) : prop =
  d `divides` a /\
  d `divides` b /\
  (forall x. (x `divides` a /\ x `divides` b) ==> x `divides` d)

(*| For a nonzero `b`, `a % b = 0` implies that `b` divides `a`.

    The converse is `FStar.Math.Euclid.divides_mod`. *)
val mod_divides (a:int) (b:nonzero) : Lemma (requires a % b = 0) (ensures b `divides` a)

(*| For a nonzero `b`, if `b` divides `a` then `a % b = 0`.

    The converse is `FStar.Math.Euclid.mod_divides`. *)
val divides_mod (a:int) (b:nonzero) : Lemma (requires b `divides` a) (ensures a % b = 0)

(*| Two greatest common divisors of the same pair are equal up to sign. *)
val is_gcd_unique (a b c d:int) : Lemma
  (requires is_gcd a b c /\ is_gcd a b d)
  (ensures  c = d \/ c = -d)

(*| `a` is a greatest common divisor of `a` and itself. *)
val is_gcd_reflexive (a:int) : Lemma (is_gcd a a a)

(*| A greatest common divisor of `a` and `b` is also one of `b` and `a`. *)
val is_gcd_symmetric (a b d:int) : Lemma
  (requires is_gcd a b d)
  (ensures  is_gcd b a d)

(*| `a` is a greatest common divisor of `a` and `0`. *)
val is_gcd_0 (a:int) : Lemma (is_gcd a 0 a)

(*| `1` is a greatest common divisor of any `a` and `1`. *)
val is_gcd_1 (a:int) : Lemma (is_gcd a 1 1)

(*| A greatest common divisor of `a` and `-b` is one of `b` and `a`.

    Note that the arguments are also swapped in the conclusion. *)
val is_gcd_minus (a b d:int) : Lemma
  (requires is_gcd a (-b) d)
  (ensures  is_gcd b a d)

(*| If `d` is a greatest common divisor of `a` and `b`, then `-d` is one of
    `b` and `a`.

    Note that the arguments are also swapped in the conclusion. *)
val is_gcd_opp (a b d:int) : Lemma
  (requires is_gcd a b d)
  (ensures  is_gcd b a (-d))

(*| Adding a multiple of `a` to `b` preserves greatest common divisors: if `d`
    is one for `a` and `b`, it is one for `a` and `b + q * a`.

    This is the invariant of Euclid's algorithm. *)
val is_gcd_plus (a b q d:int) : Lemma
  (requires is_gcd a b d)
  (ensures  is_gcd a (b + q * a) d)

///
/// Extended Euclidean algorithm
///
/// Computes the GCD of two integers (a, b) together with Bézout coefficients
/// (r, s) satisfying r a + s b = gcd(a, b)
///

(*| The extended Euclidean algorithm: returns `(r, s, d)` where `d` is a
    greatest common divisor of `a` and `b` and `r * a + s * b = d` (Bézout's
    identity).

    The sign of `d` is not fixed; see `FStar.Math.Euclid.is_gcd`. *)
val euclid_gcd (a b:int) : Pure (int & int & int)
  (requires True)
  (ensures  fun (r, s, d) -> r * a + s * b = d /\ is_gcd a b d)

///
/// A definition of primality based on the divides relation
///

(*| `p` is prime when `p > 1` and its only divisors are `1`, `-1`, `p` and
    `-p`. *)
let is_prime (p:int) =
  1 < p /\
  (forall (d:int).{:pattern (d `divides` p)}
     (d `divides` p ==> (d = 1 \/ d = -1 \/ d = p \/ d = -p)))

(*| Bézout coefficients for a prime `p` and an `a` with `0 < a < p`: returns
    `(r, s)` with `r * p + s * a = 1`.

    In particular `s` is an inverse of `a` modulo `p`. *)
val bezout_prime (p:int) (a:pos{a < p}) : Pure (int & int)
  (requires is_prime p)
  (ensures  fun (r, s) -> r * p + s * a = 1)

///
/// Euclid's lemma and its generalization to arbitrary integers
///
/// - If a prime p divides a*b, then it must divide at least one of a or b
/// - If n divides a*b and a,n are coprime then n divides b
///

(*| Generalized Euclid's lemma: if `n` divides `a * b` and `n` and `a` are
    coprime, witnessed by Bézout coefficients with `r * n + s * a = 1`, then
    `n` divides `b`.

    Divisibility is expressed with `%`. See `FStar.Math.Euclid.euclid_prime`
    for the prime case, where no coefficients are needed. *)
val euclid (n:pos) (a b r s:int) : Lemma
  (requires (a * b) % n = 0 /\ r * n + s * a = 1)
  (ensures  b % n = 0)

(*| Euclid's lemma: if a prime `p` divides `a * b`, it divides `a` or `b`.

    ```fstar
    let prime_divides_square (p: int{is_prime p}) (a: int)
      : Lemma (requires (a * a) % p = 0) (ensures a % p = 0)
      = euclid_prime p a a
    ``` *)
val euclid_prime (p:int{is_prime p}) (a b:int) : Lemma
  (requires (a * b) % p = 0)
  (ensures  a % p = 0 \/ b % p = 0)
