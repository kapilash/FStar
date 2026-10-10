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

module FStar.BitVector

/// This module defines a bit vector as a sequence of booleans of a
/// given length, and provides various utilities.
///
/// NOTE: THE TYPE [bv_t] DEFINED IS UNRELATED TO THE SMT SOLVER'S
/// THEORY OF BIT VECTORS. SEE [FStar.BV] FOR THAT.
///
/// TODO: We might rename this module to FStar.Seq.Boolean?

open FStar.Seq.Base

(*| Bit vectors of length `n`, modelled as sequences of booleans (`FStar.Seq.Base.seq bool`) of length exactly `n`.

    This is a plain sequence model, unrelated to the SMT solver's bit-vector theory; for that, see `FStar.BV.bv_t`. Equality is decidable. By the convention of the shift operators below and of `FStar.UInt.to_vec`, index `0` holds the most significant bit.

    Most operations in this module are defined recursively or with `FStar.Seq.Base` functions, and come with indexing lemmas that carry SMT patterns, so proofs usually reason bit by bit through `FStar.Seq.Base.index`. *)
[@@do_not_unrefine]
type bv_t (n: nat) = vec: seq bool {length vec = n}

(**** Common constants *)

(*| The length-`n` vector whose bits are all `false`. *)
let zero_vec (#n: pos) : Tot (bv_t n) = create n false

(*| The length-`n` vector whose only set bit is at index `i`. *)
let elem_vec (#n: pos) (i: nat{i < n}) : Tot (bv_t n) = upd (create n false) i true

(*| The length-`n` vector whose bits are all `true`. *)
let ones_vec (#n: pos) : Tot (bv_t n) = create n true

(*| Bitwise conjunction of two vectors of the same length.

    Reason about it through `FStar.BitVector.logand_vec_definition`, which fires automatically. For example, combined with sequence extensionality:

    ```fstar
    let logand_vec_self (#n: pos) (a: FStar.BitVector.bv_t n)
      : Lemma (FStar.BitVector.logand_vec a a == a)
      = FStar.Seq.Base.lemma_eq_intro (FStar.BitVector.logand_vec a a) a
    ``` *)
let rec logand_vec (#n: pos) (a b: bv_t n) : Tot (bv_t n) =
  if n = 1
  then create 1 (index a 0 && index b 0)
  else append (create 1 (index a 0 && index b 0)) (logand_vec #(n - 1) (slice a 1 n) (slice b 1 n))

(*| Bit `i` of `logand_vec a b` is `index a i && index b i`.

    Triggered automatically on `index (logand_vec a b) i`. *)
val logand_vec_definition (#n: pos) (a b: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (logand_vec #n a b) i = (index a i && index b i))
      [SMTPat (index (logand_vec #n a b) i)]

(*| Bitwise exclusive or of two vectors of the same length.

    See `FStar.BitVector.logxor_vec_definition` for its bitwise behaviour. *)
let rec logxor_vec (#n: pos) (a b: bv_t n) : Tot (bv_t n) =
  if n = 1
  then create 1 (index a 0 <> index b 0)
  else append (create 1 (index a 0 <> index b 0)) (logxor_vec #(n - 1) (slice a 1 n) (slice b 1 n))

(*| Bit `i` of `logxor_vec a b` is `index a i <> index b i`.

    Triggered automatically on `index (logxor_vec a b) i`. *)
val logxor_vec_definition (#n: pos) (a b: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (logxor_vec #n a b) i = (index a i <> index b i))
      [SMTPat (index (logxor_vec #n a b) i)]

(*| Bitwise disjunction of two vectors of the same length.

    See `FStar.BitVector.logor_vec_definition` for its bitwise behaviour. *)
let rec logor_vec (#n: pos) (a b: bv_t n) : Tot (bv_t n) =
  if n = 1
  then create 1 (index a 0 || index b 0)
  else append (create 1 (index a 0 || index b 0)) (logor_vec #(n - 1) (slice a 1 n) (slice b 1 n))

(*| Bit `i` of `logor_vec a b` is `index a i || index b i`.

    Triggered automatically on `index (logor_vec a b) i`. *)
val logor_vec_definition (#n: pos) (a b: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (logor_vec #n a b) i = (index a i || index b i))
      [SMTPat (index (logor_vec #n a b) i)]

(*| Bitwise negation of a vector.

    See `FStar.BitVector.lognot_vec_definition` for its bitwise behaviour. *)
let rec lognot_vec (#n: pos) (a: bv_t n) : Tot (bv_t n) =
  if n = 1
  then create 1 (not (index a 0))
  else append (create 1 (not (index a 0))) (lognot_vec #(n - 1) (slice a 1 n))

(*| Bit `i` of `lognot_vec a` is `not (index a i)`.

    Triggered automatically on `index (lognot_vec a) i`. *)
val lognot_vec_definition (#n: pos) (a: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (lognot_vec #n a) i = not (index a i))
      [SMTPat (index (lognot_vec #n a) i)]

(* Bitwise lemmas *)

(*| If the leading `m - n` bits of `x` and `y` are all `false`, so are those of `logxor_vec x y`.

    The precondition and conclusion are stated over indices `m - 1 - i` for `n <= i < m`, that is positions `0` to `m - 1 - n`, the most significant bits. In integer terms: the xor of two values below `pow2 n` stays below `pow2 n`. Call it explicitly; it has no SMT pattern. *)
val lemma_xor_bounded (m: pos) (n: nat) (x y: bv_t m)
    : Lemma
      (requires
        (forall (i: nat).
            (i < m /\ i >= n) ==>
            (index x (m - 1 - i) = false /\ index y (m - 1 - i) = false)))
      (ensures
        (forall (i: nat). (i < m /\ i >= n) ==> (index (logxor_vec x y) (m - 1 - i) = false)))

(*| Holds when every bit set in `a` is also set in `b`, that is the set bits of `a` form a subset of those of `b`.

    Stated as: every index where `b` is `false` is also `false` in `a`. *)
let is_subset_vec (#n: pos) (a b: bv_t n) =
  forall (i: nat). i < n ==> index b i = false ==> index a i = false

(*| Holds when every bit set in `b` is also set in `a`, that is the set bits of `a` form a superset of those of `b`. *)
let is_superset_vec (#n: pos) (a b: bv_t n) =
  forall (i: nat). i < n ==> index b i = true ==> index a i = true

(*| Slicing preserves `FStar.BitVector.is_subset_vec`: if `is_subset_vec a b` then the slices of `a` and `b` from `i` to `j` are also related.

    For `n = 1` the conclusion is stated as `True`, so the lemma says nothing in that case. Call it explicitly; it has no SMT pattern. *)
val lemma_slice_subset_vec (#n: pos) (a b: bv_t n) (i: nat) (j: nat{i < j && j <= n})
    : Lemma (requires is_subset_vec a b)
      (ensures
        (match n with
          | 1 -> True
          | _ -> is_subset_vec #(j - i) (slice a i j) (slice b i j)))

(*| Slicing preserves `FStar.BitVector.is_superset_vec`: if `is_superset_vec a b` then the slices of `a` and `b` from `i` to `j` are also related.

    For `n = 1` the conclusion is stated as `True`, so the lemma says nothing in that case. Call it explicitly; it has no SMT pattern. *)
val lemma_slice_superset_vec (#n: pos) (a b: bv_t n) (i: nat) (j: nat{i < j && j <= n})
    : Lemma (requires is_superset_vec a b)
      (ensures
        (match n with
          | 1 -> True
          | _ -> is_superset_vec #(j - i) (slice a i j) (slice b i j)))

(**** Shift operators *)

(* Note: the shift amount is extracted as a bitvector
   NS: Not sure what this remark means. *)

(*| Shifts `a` left by `s` bits, toward index `0`, filling the vacated positions at the end with `false`.

    Shifting by `s >= n` gives `FStar.BitVector.zero_vec`. The indexing lemmas `shift_left_vec_lemma_1` and `shift_left_vec_lemma_2` describe each bit and fire automatically. *)
let shift_left_vec (#n: pos) (a: bv_t n) (s: nat) : Tot (bv_t n) =
  if s >= n then zero_vec #n else if s = 0 then a else append (slice a s n) (zero_vec #s)

(*| The fill bits of `shift_left_vec a s`, at indices `i >= n - s`, are `false`.

    Triggered automatically on `index (shift_left_vec a s) i`. *)
val shift_left_vec_lemma_1 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i >= n - s})
    : Lemma (ensures index (shift_left_vec #n a s) i = false)
      [SMTPat (index (shift_left_vec #n a s) i)]

(*| Below `n - s`, bit `i` of `shift_left_vec a s` is bit `i + s` of `a`.

    Triggered automatically on `index (shift_left_vec a s) i`. *)
val shift_left_vec_lemma_2 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i < n - s})
    : Lemma (ensures index (shift_left_vec #n a s) i = index a (i + s))
      [SMTPat (index (shift_left_vec #n a s) i)]

(*| Shifts `a` right by `s` bits, away from index `0`, filling the vacated positions at the front with `false` (a logical shift).

    Shifting by `s >= n` gives `FStar.BitVector.zero_vec`. See `FStar.BitVector.shift_arithmetic_right_vec` for the sign-filling variant. *)
let shift_right_vec (#n: pos) (a: bv_t n) (s: nat) : Tot (bv_t n) =
  if s >= n then zero_vec #n else if s = 0 then a else append (zero_vec #s) (slice a 0 (n - s))

(*| The fill bits of `shift_right_vec a s`, at indices `i < s`, are `false`.

    Triggered automatically on `index (shift_right_vec a s) i`. *)
val shift_right_vec_lemma_1 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i < s})
    : Lemma (ensures index (shift_right_vec #n a s) i = false)
      [SMTPat (index (shift_right_vec #n a s) i)]

(*| From index `s` on, bit `i` of `shift_right_vec a s` is bit `i - s` of `a`.

    Triggered automatically on `index (shift_right_vec a s) i`. *)
val shift_right_vec_lemma_2 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i >= s})
    : Lemma (ensures index (shift_right_vec #n a s) i = index a (i - s))
      [SMTPat (index (shift_right_vec #n a s) i)]

(*| Arithmetic right shift: shifts `a` right by `s` bits, filling the vacated positions with the most significant bit `index a 0`.

    When `index a 0` is `false` it coincides with `FStar.BitVector.shift_right_vec`; when it is `true` and `s >= n` the result is `FStar.BitVector.ones_vec`. *)
let shift_arithmetic_right_vec (#n: pos) (a: bv_t n) (s: nat) : Tot (bv_t n) =
  if index a 0
  then if s >= n then ones_vec #n else if s = 0 then a else append (ones_vec #s) (slice a 0 (n - s))
  else shift_right_vec a s

(*| The fill bits of `shift_arithmetic_right_vec a s`, at indices `i < s`, equal the most significant bit `index a 0`.

    Triggered automatically on `index (shift_arithmetic_right_vec a s) i`. *)
val shift_arithmetic_right_vec_lemma_1 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i < s})
    : Lemma (ensures index (shift_arithmetic_right_vec #n a s) i = index a 0)
      [SMTPat (index (shift_arithmetic_right_vec #n a s) i)]

(*| From index `s` on, bit `i` of `shift_arithmetic_right_vec a s` is bit `i - s` of `a`.

    Triggered automatically on `index (shift_arithmetic_right_vec a s) i`. *)
val shift_arithmetic_right_vec_lemma_2 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i >= s})
    : Lemma (ensures index (shift_arithmetic_right_vec #n a s) i = index a (i - s))
      [SMTPat (index (shift_arithmetic_right_vec #n a s) i)]

(**** Rotate operators *)

(*| Rotates `a` left by `s` bits, toward index `0`; bits leaving at the front re-enter at the end.

    The amount is taken modulo `n`. See `FStar.BitVector.rotate_left_vec_lemma` for the bitwise behaviour. *)
let rotate_left_vec (#n: pos) (a: bv_t n) (s: nat) : Tot (bv_t n) =
  let s = s % n in
  append (slice a s n) (slice a 0 s)

(*| Rotates `a` right by `s` bits, away from index `0`; bits leaving at the end re-enter at the front.

    The amount is taken modulo `n`. See `FStar.BitVector.rotate_right_vec_lemma` for the bitwise behaviour. *)
let rotate_right_vec (#n: pos) (a: bv_t n) (s: nat) : Tot (bv_t n) =
  let s = s % n in
  append (slice a (n - s) n) (slice a 0 (n - s))

(*| Bit `i` of `rotate_left_vec a s` is bit `(i + s) % n` of `a`.

    Triggered automatically on `index (rotate_left_vec a s) i`. *)
val rotate_left_vec_lemma (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n})
    : Lemma (ensures index (rotate_left_vec #n a s) i = index a ((i + s) % n))
      [SMTPat (index (rotate_left_vec #n a s) i)]

(*| Bit `i` of `rotate_right_vec a s` is bit `(i + n - (s % n)) % n` of `a`.

    Triggered automatically on `index (rotate_right_vec a s) i`. *)
val rotate_right_vec_lemma (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n})
    : Lemma (ensures index (rotate_right_vec #n a s) i = index a ((i + n - (s % n)) % n))
      [SMTPat (index (rotate_right_vec #n a s) i)]

(*| Rotating left by the full length `n` is the identity.

    Triggered automatically on `rotate_left_vec a n`. *)
val rotate_left_vec_full_identity (#n: pos) (a: bv_t n)
    : Lemma (ensures rotate_left_vec #n a n = a)
      [SMTPat (rotate_left_vec #n a n)]

(*| Rotating right by the full length `n` is the identity.

    Triggered automatically on `rotate_right_vec a n`. *)
val rotate_right_vec_full_identity (#n: pos) (a: bv_t n)
    : Lemma (ensures rotate_right_vec #n a n = a)
      [SMTPat (rotate_right_vec #n a n)]

(*| Rotating right by `s` undoes rotating left by `s`.

    Call it explicitly; it has no SMT pattern. See also `FStar.BitVector.rotate_right_left_vec_inverse`. *)
val rotate_left_right_vec_inverse (#n: pos) (a: bv_t n) (s: nat)
    : Lemma (ensures rotate_right_vec #n (rotate_left_vec #n a s) s = a)

(*| Rotating left by `s` undoes rotating right by `s`.

    Call it explicitly; it has no SMT pattern. See also `FStar.BitVector.rotate_left_right_vec_inverse`. *)
val rotate_right_left_vec_inverse (#n: pos) (a: bv_t n) (s: nat)
    : Lemma (ensures rotate_left_vec #n (rotate_right_vec #n a s) s = a)
