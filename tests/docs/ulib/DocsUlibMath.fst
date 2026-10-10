module DocsUlibMath

(* Examples from the documentation of FStar.Math.* *)

let mod_of_sum (a b: int) (n: pos)
  : Lemma ((a % n + b % n) % n == (a + b) % n)
  = FStar.Math.Lemmas.modulo_distributivity a b n

let mod_of_product (a b: int) (n: pos)
  : Lemma ((a % n) * (b % n) % n == (a * b) % n)
  = FStar.Math.Lemmas.lemma_mod_mul_distr_l a b n;
    FStar.Math.Lemmas.lemma_mod_mul_distr_r (a % n) b n

let middle_bits (x: nat) (n m: nat)
  : Lemma ((x % pow2 (n + m)) / pow2 n == (x / pow2 n) % pow2 m)
  = FStar.Math.Lemmas.pow2_modulo_division_lemma_1 x n (n + m)

let div_mod_unique (a q r: int) (n: pos)
  : Lemma (requires a == q * n + r /\ 0 <= r /\ r < n)
          (ensures a / n == q /\ a % n == r)
  = FStar.Math.Lemmas.lemma_div_plus r q n;
    FStar.Math.Lemmas.lemma_mod_plus r q n;
    FStar.Math.Lemmas.small_div r n;
    FStar.Math.Lemmas.small_mod r n

open FStar.Math.Euclid

let prime_divides_square (p: int{is_prime p}) (a: int)
  : Lemma (requires (a * a) % p = 0) (ensures a % p = 0)
  = euclid_prime p a a
