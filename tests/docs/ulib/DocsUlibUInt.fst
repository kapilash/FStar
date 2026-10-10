module DocsUlibUInt

(* Examples from the documentation of FStar.UInt, FStar.IntegerIntervals
   and FStar.IntegerLiteral *)

open FStar.UInt

let add_mod_wraps () : Lemma (add_mod #8 255 1 == 0) = ()

let truncate_cast () : Lemma (to_uint_t 8 300 == 44 /\ to_uint_t 8 (-1) == 255) = ()

let low_bits (a: uint_t 32)
  : Lemma (logand #32 a 0xff == a % 256)
  = logand_mask #32 a 8

let shift_is_mul (a: uint_t 32)
  : Lemma (shift_left #32 a 4 == (a * pow2 4) % pow2 32)
  = ()

let same_bits (#n: pos) (a b: uint_t n)
  : Lemma (requires forall (i: nat{i < n}). nth a i = nth b i)
          (ensures a == b)
  = nth_lemma a b

open FStar.IntegerIntervals

let sizes () : Lemma (interval_size (interval 5 10) = 5 /\ closed_interval_size 5 10 = 6) = ()

let first_ten : under 10 = 9
