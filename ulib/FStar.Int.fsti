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
module FStar.Int

(* NOTE: anything that you fix/update here should be reflected in [FStar.UInt.fsti], which is mostly
 * a copy-paste of this module. *)

open FStar.BitVector
open FStar.Math.Lemmas

(*| Gives the concrete value of `pow2 x` for the exponents used by machine integers: `0`, `1`, `8`, `16`, `31`, `32`, `63` and `64`.

    For other exponents it states nothing. Triggered automatically on `pow2 x`. *)
val pow2_values: x:nat -> Lemma
  (let p = pow2 x in
   match x with
   | 0  -> p=1
   | 1  -> p=2
   | 8  -> p=256
   | 16 -> p=65536
   | 31 -> p=2147483648
   | 32 -> p=4294967296
   | 63 -> p=9223372036854775808
   | 64 -> p=18446744073709551616
   | _  -> True)
  [SMTPat (pow2 x)]

/// Specs

(*| The largest signed integer representable in `n` bits in two's complement: `pow2 (n - 1) - 1`. *)
let max_int (n:pos) : Tot int = pow2 (n-1) - 1
(*| The smallest signed integer representable in `n` bits in two's complement: `- (pow2 (n - 1))`. *)
let min_int (n:pos) : Tot int = - (pow2 (n-1))

(*| Boolean test that `x` lies in the `n`-bit signed range `[FStar.Int.min_int n, FStar.Int.max_int n]`.

    See `FStar.Int.size` for the same condition as a proposition. *)
let fits (x:int) (n:pos) : Tot bool = min_int n <= x && x <= max_int n
(*| The proposition that `x` lies in the `n`-bit signed range; the `prop` form of `FStar.Int.fits`.

    It is the refinement of `FStar.Int.int_t` and the precondition of the non-wrapping operations such as `FStar.Int.add`. *)
let size (x:int) (n:pos) : prop = fits x n

(* Machine integer type *)
(*| The mathematical model of signed `n`-bit integers: mathematical integers `x` with `FStar.Int.min_int n <= x <= FStar.Int.max_int n`.

    Values are ordinary `int`s, so equality is decidable and arithmetic on them is unbounded. The operations of this module take and return `int_t n` and specify either a precondition (for example `FStar.Int.add`) or two's complement wrap-around (for example `FStar.Int.add_mod`). Machine integer modules such as `FStar.Int32` expose their values through `v : t -> int_t 32`. The unsigned counterpart is `FStar.UInt.uint_t`. *)
type int_t (n:pos) = x:int{size x n}

/// Multiplicative operator semantics, see C11 6.5.5

(* Truncation towards zero division: (/-) *)
(*| Integer division truncating towards zero, as in C (C11 6.5.5); `b` must be nonzero.

    The quotient is `abs a / abs b`, negated when exactly one of `a` and `b` is negative. Unlike the Euclidean `/` on `int`, `(-7) /- 2 == -3`. Used to specify `FStar.Int.div` and `FStar.Int.mod`. *)
let ( /- ) (a:int) (b:int{b <> 0}) : Tot int =
  if (a >= 0 && b < 0) || (a < 0 && b >= 0) then - (abs a / abs b)
  else abs a / abs b

(* Wrap-around modulo: wraps into [-p/2; p/2[ *)
(*| Two's complement wrap-around modulo: reduces `v` modulo `p` into the range `[-p/2, p/2)`; `p` must be positive and even.

    It computes `v % p` and subtracts `p` when the result is at least `p/2`. With `p = pow2 n` this maps any integer to the `n`-bit signed integer with the same low `n` bits, as in `FStar.Int.add_mod` and `FStar.Int.to_int_t`. *)
let ( @% ) (v:int) (p:int{p>0/\ p%2=0}) : Tot int =
  let m = v % p in if m >= p/2 then m - p else m

/// Constants

(*| The constant `0` as an `n`-bit signed integer. *)
let zero (n:pos) : Tot (int_t n) = 0

#push-options "--fuel 1"

(*| The constant `pow2 p` as an `n`-bit signed integer, for `p < n - 1` (so that it is at most `FStar.Int.max_int n`). *)
let pow2_n (#n:pos) (p:nat{p < n-1}) : Tot (int_t n) =
  pow2_le_compat (n - 2) p; pow2 p

(*| The constant `pow2 m - 1` as an `n`-bit signed integer, for `m < n` and `n > 1`: the mask of the `m` least significant bits. *)
let pow2_minus_one (#n:pos{1 < n}) (m:nat{m < n}) : Tot (int_t n) =
  pow2_le_compat (n - 1) m;
  pow2 m - 1 

(*| The constant `1` as an `n`-bit signed integer; requires `n > 1`. *)
let one (n:pos{1 < n}) : Tot (int_t n) = 1

#pop-options

(*| The constant `-1` as an `n`-bit signed integer: the value whose bits are all set in two's complement. *)
let ones (n:pos) : Tot (int_t n) = -1

(* Increment and decrement *)
(*| Adds one; requires `a < FStar.Int.max_int n`, so it never overflows.

    `Pure` with result `a + 1`. See `FStar.Int.incr_mod` for a total variant. *)
let incr (#n:pos) (a:int_t n)
    : Pure (int_t n)
      (requires (b2t (a < max_int n))) (ensures (fun _ -> True))
  = a + 1

(*| Subtracts one; requires `a > FStar.Int.min_int n`, so it never overflows.

    `Pure` with result `a - 1`. See `FStar.Int.decr_mod` for a total variant. *)
let decr (#n:pos) (a:int_t n)
    : Pure (int_t n)
      (requires (b2t (a > min_int n))) (ensures (fun _ -> True))
  = a - 1

(*| Total increment defined as `(a + 1) % pow2 (n - 1)`, using the Euclidean `%`.

    The result is always in `[0, pow2 (n - 1))`: it is not two's complement wrap-around, and it differs from `a + 1` for every negative `a` other than `-1`. For two's complement increment use `FStar.Int.add_mod a (FStar.Int.one n)`. *)
let incr_mod (#n:pos) (a:int_t n) : Tot (int_t n) =
  (a + 1) % (pow2 (n-1))

(*| Total decrement defined as `(a - 1) % pow2 (n - 1)`, using the Euclidean `%`.

    The result is always in `[0, pow2 (n - 1))`: it is not two's complement wrap-around, and it differs from `a - 1` whenever `a <= 0`. For two's complement decrement use `FStar.Int.sub_mod a (FStar.Int.one n)`. *)
let decr_mod (#n:pos) (a:int_t n) : Tot (int_t n) =
  (a - 1) % (pow2 (n-1))

(* Addition primitives *)
(*| Addition without overflow: the result is `a + b`, and the sum must fit in `n` bits.

    `Pure` with precondition `FStar.Int.size (a + b) n`. See `FStar.Int.add_mod` for the wrapping variant. *)
let add (#n:pos) (a:int_t n) (b:int_t n)
    : Pure (int_t n)
      (requires (size (a + b) n))
      (ensures (fun _ -> True))
  = a + b

#push-options "--fuel 1"

(*| Addition with two's complement wrap-around: the result is `(a + b) @% pow2 n`.

    Total; when the sum fits in `n` bits it equals `a + b`. The non-wrapping variant is `FStar.Int.add`.

    ```fstar
    let wrap_example () : Lemma (add_mod #8 127 1 == -128 /\ 200 @% 256 == -56) =
      assert_norm (add_mod #8 127 1 == -128 /\ 200 @% 256 == -56)
    ``` *)
let add_mod (#n:pos) (a:int_t n) (b:int_t n) : Tot (int_t n) =
  (a + b) @% (pow2 n)

(* Minus primitives *)
(*| Subtraction without overflow: the result is `a - b`, and the difference must fit in `n` bits.

    `Pure` with precondition `FStar.Int.size (a - b) n`. See `FStar.Int.sub_mod` for the wrapping variant. *)
let sub (#n:pos) (a:int_t n) (b:int_t n)
    : Pure (int_t n)
      (requires (size (a - b) n))
      (ensures (fun _ -> True))    
  = a - b

(*| Subtraction with two's complement wrap-around: the result is `(a - b) @% pow2 n`.

    Total; when the difference fits in `n` bits it equals `a - b`. The non-wrapping variant is `FStar.Int.sub`. *)
let sub_mod (#n:pos) (a:int_t n) (b:int_t n) : Tot (int_t n) =
  (a - b) @% (pow2 n)

(* Multiplication primitives *)
(*| Multiplication without overflow: the result is `a * b`, and the product must fit in `n` bits.

    `Pure` with precondition `FStar.Int.size (a * b) n`. See `FStar.Int.mul_mod` for the wrapping variant. *)
let mul (#n:pos) (a:int_t n) (b:int_t n)
    : Pure (int_t n)
      (requires (size (a * b) n))
      (ensures (fun _ -> True))
  = a * b

(*| Multiplication with two's complement wrap-around: the result is `(a * b) @% pow2 n`.

    Total; when the product fits in `n` bits it equals `a * b`. The non-wrapping variant is `FStar.Int.mul`. *)
let mul_mod (#n:pos) (a:int_t n) (b:int_t n) : Tot (int_t n) =
  (a * b) @% (pow2 n)

#pop-options

(* Division primitives. Truncates towards zero. *)
(*| Signed division truncating towards zero, as in C: the result is `a /- b`.

    `Pure`; `b` must be nonzero and the quotient must fit in `n` bits, which excludes only `FStar.Int.min_int n` divided by `-1`. See `FStar.Int.udiv` for a total variant that excludes `FStar.Int.min_int n` as dividend. *)
let div (#n:pos) (a:int_t n) (b:int_t n{b <> 0})
    : Pure (int_t n)
      (requires (size (a /- b) n))
      (ensures (fun c -> b <> 0 ==> a /- b = c))
= a /- b

(*| For a dividend greater than `FStar.Int.min_int n` and a nonzero divisor, the Euclidean quotient `a / b` fits in `n` bits.

    Note that this is about the Euclidean `/` on `int`, not the truncating `/-` used by `FStar.Int.div`. *)
val div_size: #n:pos -> a:int_t n{min_int n < a} -> b:int_t n{b <> 0} ->
  Lemma (requires (size a n)) (ensures (size (a / b) n))

(*| Total signed division truncating towards zero: the result is `a /- b`.

    The dividend must be greater than `FStar.Int.min_int n` and the divisor nonzero, so the quotient always fits. See `FStar.Int.div` for the variant whose precondition is on the quotient. *)
let udiv (#n:pos) (a:int_t n{min_int n < a}) (b:int_t n{b <> 0})
    : Tot (c:int_t n{b <> 0 ==> a /- b = c})
  = div_size #n a b;
    a /- b

(* Remainder primitives (NOT modulo, division truncates towards zero
   and remainders have the same sign as the dividend) *)
(*| Signed remainder, as the C `%` operator: `a - (a /- b) * b`; `b` must be nonzero.

    This is not the Euclidean modulo: division truncates towards zero, so the remainder has the sign of the dividend `a` (or is zero). Total.

    ```fstar
    let truncating_division () : Lemma ((-7) /- 2 == -3 /\ mod #8 (-7) 2 == -1) =
      assert_norm ((-7) /- 2 == -3 /\ mod #8 (-7) 2 == -1)
    ``` *)
let mod (#n:pos) (a:int_t n) (b:int_t n{b <> 0}) : Tot (int_t n) =
  a - ((a /- b) * b)

(* Comparison operators *)
(*| Boolean equality of two `n`-bit signed integers. *)
let eq  #n (a:int_t n) (b:int_t n) : Tot bool = a = b
(*| Boolean disequality of two `n`-bit signed integers. *)
let ne  #n (a:int_t n) (b:int_t n) : Tot bool = a <> b
(*| Boolean test `a > b` on `n`-bit signed integers (signed comparison). *)
let gt  #n (a:int_t n) (b:int_t n) : Tot bool = a > b
(*| Boolean test `a >= b` on `n`-bit signed integers (signed comparison). *)
let gte #n (a:int_t n) (b:int_t n) : Tot bool = a >= b
(*| Boolean test `a < b` on `n`-bit signed integers (signed comparison). *)
let lt  #n (a:int_t n) (b:int_t n) : Tot bool = a < b
(*| Boolean test `a <= b` on `n`-bit signed integers (signed comparison). *)
let lte #n (a:int_t n) (b:int_t n) : Tot bool = a <= b

/// Casts

(*| Reinterprets a signed `n`-bit integer as the unsigned `n`-bit integer with the same two's complement bits.

    Nonnegative values are unchanged; a negative `x` becomes `x + pow2 n`. The inverse is `FStar.Int.from_uint`. *)
let to_uint (#n:pos) (x:int_t n) : Tot (UInt.uint_t n) = 
  if 0 <= x then x else x + pow2 n 

(*| Reinterprets an unsigned `n`-bit integer as the signed `n`-bit integer with the same two's complement bits.

    Values up to `FStar.Int.max_int n` are unchanged; larger values `x` become `x - pow2 n`. The inverse is `FStar.Int.to_uint`. *)
let from_uint (#n:pos) (x:UInt.uint_t n) : Tot (int_t n) = 
  if x <= max_int n then x else x - pow2 n 

(*| Converting to unsigned and back is the identity: `from_uint (to_uint x) == x`.

    Triggered automatically on `FStar.Int.to_uint x`. *)
val to_uint_injective: #n:pos -> x:int_t n
  -> Lemma (ensures from_uint (to_uint x) == x) [SMTPat (to_uint x)]

(*| Wraps an arbitrary integer into the `n`-bit signed range: the result is `a @% pow2 m`.

    It keeps the low `m` bits of `a` and reads them as a two's complement number; values already in range are unchanged. *)
let to_int_t (m:pos) (a:int) : Tot (int_t m) = a @% pow2 m

open FStar.Seq

(* WARNING: Mind the big endian vs little endian definition *)

(*| The `n`-bit two's complement bit vector of a signed integer, most significant bit first.

    Index `0` is the sign bit and index `n - 1` the least significant bit. Defined as `FStar.UInt.to_vec (FStar.Int.to_uint num)`; the inverse is `FStar.Int.from_vec`. *)
let to_vec (#n:pos) (num:int_t n) : Tot (bv_t n) =
  UInt.to_vec (to_uint num)

(*| The signed integer represented by an `n`-bit two's complement bit vector, most significant bit first.

    The inverse of `FStar.Int.to_vec`. *)
let from_vec (#n:pos) (vec:bv_t n) : Tot (int_t n) =
  let x = UInt.from_vec vec in
  if max_int n < x then x - pow2 n else x

(*| Equal integers have equal bit vectors (`FStar.Seq.Base.equal`). *)
val to_vec_lemma_1: #n:pos -> a:int_t n -> b:int_t n ->
  Lemma (requires a = b) (ensures equal (to_vec a) (to_vec b))

(*| `FStar.Int.to_vec` is injective: integers with equal bit vectors are equal. *)
val to_vec_lemma_2: #n:pos -> a:int_t n -> b:int_t n ->
  Lemma (requires equal (to_vec a) (to_vec b)) (ensures a = b)

(*| Pointwise form of `FStar.Int.inverse_vec_lemma`: bit `i` of `to_vec (from_vec vec)` is bit `i` of `vec`.

    Triggered automatically on `index (to_vec (from_vec vec)) i`. *)
val inverse_aux: #n:nat -> vec:bv_t n -> i:nat{i < n} ->
  Lemma (requires True) (ensures index vec i = index (to_vec (from_vec vec)) i)
        [SMTPat (index (to_vec (from_vec vec)) i)]

(*| Converting a bit vector to an integer and back gives an equal vector.

    Triggered automatically on `FStar.Int.to_vec (FStar.Int.from_vec vec)`. *)
val inverse_vec_lemma: #n:pos -> vec:bv_t n ->
  Lemma (requires True) (ensures equal vec (to_vec (from_vec vec)))
        [SMTPat (to_vec (from_vec vec))]

(*| Converting an integer to a bit vector and back gives the same integer.

    Triggered automatically on `FStar.Int.from_vec (FStar.Int.to_vec num)`. *)
val inverse_num_lemma: #n:pos -> num:int_t n ->
  Lemma (requires True) (ensures num = from_vec (to_vec num))
        [SMTPat (from_vec (to_vec num))]

(*| Equal bit vectors (`FStar.Seq.Base.equal`) denote equal integers. *)
val from_vec_lemma_1: #n:pos -> a:bv_t n -> b:bv_t n ->
  Lemma (requires equal a b) (ensures from_vec a = from_vec b)

(*| `FStar.Int.from_vec` is injective: bit vectors denoting the same integer are equal. *)
val from_vec_lemma_2: #n:pos -> a:bv_t n -> b:bv_t n ->
  Lemma (requires from_vec a = from_vec b) (ensures equal a b)

(* Relations between constants in BitVector and in UInt. *)
(*| The bit vector of `FStar.Int.zero n` is `FStar.BitVector.zero_vec`, bit by bit.

    Triggered automatically on `index (to_vec (zero n)) i`. *)
val zero_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures index (to_vec (zero n)) i = index (zero_vec #n) i)
        [SMTPat (index (to_vec (zero n)) i)]

(*| `FStar.BitVector.zero_vec` denotes `FStar.Int.zero n`.

    Triggered automatically on `from_vec zero_vec`. *)
val zero_from_vec_lemma: #n:pos ->
  Lemma (requires True) (ensures from_vec (zero_vec #n) = zero n)
        [SMTPat (from_vec (zero_vec #n))]

(*| The bit vector of `FStar.Int.one n` has only its last (least significant) bit `n - 1` set, bit by bit.

    Triggered automatically on `index (to_vec (one n)) i`. *)
val one_to_vec_lemma: #n:pos{1 < n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (one n)) i = index (elem_vec #n (n - 1)) i)
	[SMTPat (index (to_vec (one n)) i)]

(*| The bit vector of `FStar.Int.pow2_n p` has only bit `n - p - 1` set, bit by bit (bits are numbered from the most significant).

    Triggered automatically on `index (to_vec (pow2_n p)) i`. *)
val pow2_to_vec_lemma: #n:pos -> p:nat{p < n-1} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (pow2_n #n p)) i = index (elem_vec #n (n - p - 1)) i)
	[SMTPat (index (to_vec (pow2_n #n p)) i)]

(*| The bit vector with only bit `p` set denotes `FStar.Int.pow2_n (n - p - 1)`, for `0 < p < n - 1`.

    Triggered automatically on `from_vec (elem_vec p)`. *)
val pow2_from_vec_lemma: #n:pos -> p:pos{p < n-1} ->
  Lemma (requires True) (ensures from_vec (elem_vec #n p) = pow2_n #n (n - p - 1))
        [SMTPat (from_vec (elem_vec #n p))]

(*| The bit vector of `FStar.Int.ones n` (that is, `-1`) is `FStar.BitVector.ones_vec`, bit by bit.

    Triggered automatically on `index (to_vec (ones n)) i`. *)
val ones_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (ones n)) i = index (ones_vec #n) i)
	[SMTPat (index (to_vec (ones n)) i)]

(*| `FStar.BitVector.ones_vec` denotes `FStar.Int.ones n`, that is `-1`.

    Triggered automatically on `from_vec ones_vec`. *)
val ones_from_vec_lemma: #n:pos ->
  Lemma (requires True) (ensures from_vec (ones_vec #n) = ones n)
        [SMTPat (from_vec (ones_vec #n))]


(* (nth a i) returns a boolean indicating the i-th bit of a. *)
(*| Bit `i` of the two's complement representation of `a`, numbered from the most significant bit.

    `nth a 0` is the sign bit and `nth a (n - 1)` the least significant bit. Defined as `index (to_vec a) i`. *)
let nth (#n:pos) (a:int_t n) (i:nat{i < n}) : Tot bool = index (to_vec #n a) i

(*| Bit extensionality: two `n`-bit signed integers with the same bits are equal. *)
val nth_lemma: #n:pos -> a:int_t n -> b:int_t n ->
  Lemma (requires forall (i:nat{i < n}). nth a i = nth b i)
        (ensures a = b)

(* Lemmas for constants *)
(*| Every bit of `FStar.Int.zero n` is unset.

    Triggered automatically on `nth (zero n) i`. *)
val zero_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures nth (zero n) i = false)
        [SMTPat (nth (zero n) i)]

(*| Only the least significant bit (index `n - 1`) of `FStar.Int.one n` is set.

    Triggered automatically on `nth (one n) i`. *)
val one_nth_lemma: #n:pos{1 < n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (i = n - 1 ==> nth (one n) i = true) /\
	         (i < n - 1 ==> nth (one n) i = false))
        [SMTPat (nth (one n) i)]

(*| Every bit of `FStar.Int.ones n` (that is, `-1`) is set.

    Triggered automatically on `nth (ones n) i`. *)
val ones_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures (nth (ones n) i) = true)
        [SMTPat (nth (ones n) i)]

(* Bitwise operators *)
(*| Bitwise AND of the two's complement representations of `a` and `b`.

    Characterized bit by bit by `FStar.Int.logand_definition`. Total. *)
let logand (#n:pos) (a:int_t n) (b:int_t n) : Tot (int_t n) =
  from_vec #n (logand_vec #n (to_vec #n a) (to_vec #n b))

(*| Bitwise exclusive OR of the two's complement representations of `a` and `b`.

    Characterized bit by bit by `FStar.Int.logxor_definition`. Total. *)
let logxor (#n:pos) (a:int_t n) (b:int_t n) : Tot (int_t n) =
  from_vec #n (logxor_vec #n (to_vec #n a) (to_vec #n b))

(*| Bitwise OR of the two's complement representations of `a` and `b`.

    Characterized bit by bit by `FStar.Int.logor_definition`. Total. *)
let logor (#n:pos) (a:int_t n) (b:int_t n) : Tot (int_t n) =
  from_vec #n (logor_vec #n (to_vec #n a) (to_vec #n b))

(*| Bitwise complement of the two's complement representation of `a`.

    Characterized bit by bit by `FStar.Int.lognot_definition`. Total. *)
let lognot (#n:pos) (a:int_t n) : Tot (int_t n)=
  from_vec #n (lognot_vec #n (to_vec #n a))

(* Bitwise operators definitions *)
(*| Bit `i` of `logand a b` is the conjunction of bit `i` of `a` and of `b`.

    Triggered automatically on `nth (logand a b) i`. *)
val logand_definition: #n:pos -> a:int_t n -> b:int_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logand a b) i = (nth a i && nth b i)))
	[SMTPat (nth (logand a b) i)]

(*| Bit `i` of `logxor a b` is set exactly when bits `i` of `a` and `b` differ.

    Triggered automatically on `nth (logxor a b) i`. *)
val logxor_definition: #n:pos -> a:int_t n -> b:int_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logxor a b) i = (nth a i <> nth b i)))
	[SMTPat (nth (logxor a b) i)]

(*| Bit `i` of `logor a b` is the disjunction of bit `i` of `a` and of `b`.

    Triggered automatically on `nth (logor a b) i`. *)
val logor_definition: #n:pos -> a:int_t n -> b:int_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (logor a b) i = (nth a i || nth b i)))
	[SMTPat (nth (logor a b) i)]

(*| Bit `i` of `lognot a` is the negation of bit `i` of `a`.

    Triggered automatically on `nth (lognot a) i`. *)
val lognot_definition: #n:pos -> a:int_t n -> i:nat{i < n} ->
  Lemma (requires True)
	(ensures (nth (lognot a) i = not(nth a i)))
	[SMTPat (nth (lognot a) i)]

(* Two's complement unary minus *)
(*| Two's complement negation: `add_mod (lognot a) 1`; requires `n > 1`.

    Total. It equals `- a` except for `FStar.Int.min_int n`, which is its own negation by wrap-around. *)
inline_for_extraction
let minus (#n:pos{1 < n}) (a:int_t n) : Tot (int_t n) =
  add_mod (lognot a) 1

(* Bitwise operators lemmas *)
(* TODO: lemmas about the relations between different operators *)
(* Bitwise AND operator *)
(*| `FStar.Int.logand` is commutative. *)
val logand_commutative: #n:pos -> a:int_t n -> b:int_t n ->
  Lemma (requires True) (ensures (logand #n a b = logand #n b a))

(*| `FStar.Int.logand` is associative. *)
val logand_associative: #n:pos -> a:int_t n -> b:int_t n -> c:int_t n ->
  Lemma (logand #n (logand #n a b) c = logand #n a (logand #n b c))

(*| `FStar.Int.logand` is idempotent: `logand a a = a`. *)
val logand_self: #n:pos -> a:int_t n ->
  Lemma (logand #n a a = a)

(*| `FStar.Int.zero n` is absorbing for `FStar.Int.logand`: `logand a (zero n) = zero n`. *)
val logand_lemma_1: #n:pos -> a:int_t n ->
  Lemma (requires True) (ensures (logand #n a (zero n) = zero n))

(*| `FStar.Int.ones n` (that is, `-1`) is neutral for `FStar.Int.logand`: `logand a (ones n) = a`. *)
val logand_lemma_2: #n:pos -> a:int_t n ->
  Lemma (logand #n a (ones n) = a)

(*| The sign bit `nth a 0` is set exactly when `a` is negative; requires `n > 1`. *)
val sign_bit_negative: #n:pos{1 < n} -> a:int_t n -> 
  Lemma (nth a 0 = true <==> a < 0)

(*| The sign bit `nth a 0` is unset exactly when `a` is nonnegative; requires `n > 1`. *)
val sign_bit_positive: #n:pos{1 < n} -> a:int_t n -> 
  Lemma (nth a 0 = false <==> 0 <= a)

(*| The bitwise AND of two nonnegative integers is nonnegative and at most each of them. *)
val logand_pos_le: #n:pos{1 < n} -> a:int_t n{0 <= a} -> b:int_t n{0 <= b} ->
  Lemma (0 <= logand a b /\ logand a b <= a /\ logand a b <= b)

(*| Masking with `FStar.Int.pow2_minus_one m` gives a result between `0` and `pow2 m - 1`, for any (possibly negative) `a`. *)
val logand_pow2_minus_one: #n:pos{1 < n} -> a:int_t n -> m:pos{m < n} ->
  Lemma (0 <= logand a (pow2_minus_one m) /\ 
    logand a (pow2_minus_one m) <= pow2_minus_one #n m)

(*| Masking a nonnegative integer with `FStar.Int.max_int n` leaves it unchanged. *)
val logand_max: #n:pos{1 < n} -> a:int_t n{0 <= a} ->
  Lemma (0 <= logand a (max_int n) /\ a = logand a (max_int n))

(* Bitwise XOR operator *)
(*| `FStar.Int.logxor` is commutative. *)
val logxor_commutative: #n:pos -> a:int_t n -> b:int_t n ->
  Lemma (requires True) (ensures (logxor #n a b = logxor #n b a))

(*| `FStar.Int.logxor` is associative. *)
val logxor_associative: #n:pos -> a:int_t n -> b:int_t n -> c:int_t n ->
  Lemma (requires True) (ensures (logxor #n (logxor #n a b) c = logxor #n a (logxor #n b c)))

(*| The exclusive OR of a value with itself is `FStar.Int.zero n`. *)
val logxor_self: #n:pos -> a:int_t n ->
  Lemma (requires True) (ensures (logxor #n a a = zero n))

(*| `FStar.Int.zero n` is neutral for `FStar.Int.logxor`: `logxor a (zero n) = a`. *)
val logxor_lemma_1: #n:pos -> a:int_t n ->
  Lemma (requires True) (ensures (logxor #n a (zero n) = a))

(*| Exclusive OR with `FStar.Int.ones n` (that is, `-1`) is bitwise complement: `logxor a (ones n) = lognot a`. *)
val logxor_lemma_2: #n:pos -> a:int_t n ->
  Lemma (requires True) (ensures (logxor #n a (ones n) = lognot #n a))

(*| Exclusive OR with `b` is self-inverse: `logxor (logxor a b) b = a`. *)
val logxor_inv: #n:pos -> a:int_t n -> b:int_t n -> Lemma
  (a = logxor #n (logxor #n a b) b)

(*| The exclusive OR of two different values is nonzero. *)
val logxor_neq_nonzero: #n:pos -> a:int_t n -> b:int_t n -> Lemma
   (a <> b ==> logxor a b <> 0)

(*| For a negative `a`, `lognot a` equals the unsigned complement `FStar.UInt.lognot` of its two's complement encoding `a + pow2 n`.

    In particular the result is nonnegative. *)
val lognot_negative: #n:pos -> a:int_t n -> Lemma
  (requires a < 0)
  (ensures  lognot a == UInt.lognot #n (a + pow2 n))

(* Shift operators *)

(*| Left shift of a nonnegative integer by `s` bits; zeros are shifted in at the least significant end.

    Total. The argument must be nonnegative: in C, left-shifting a negative value is undefined behaviour, and this specification does not model it. The value is `(a * pow2 s) @% pow2 n` (`FStar.Int.shift_left_value_lemma`), so bits shifted into the sign position can make the result negative, and `s >= n` gives `0`. *)
let shift_left (#n:pos) (a:int_t n{0 <= a}) (s:nat) : Tot (int_t n) =
  from_vec (shift_left_vec #n (to_vec #n a) s)

(*| Logical right shift of a nonnegative integer by `s` bits; zeros are shifted in at the most significant end.

    Total. The argument must be nonnegative: in C, right-shifting a negative value has an implementation-defined result. Use `FStar.Int.shift_arithmetic_right` for negative values. *)
let shift_right (#n:pos) (a:int_t n{0 <= a}) (s:nat) : Tot (int_t n) =
  from_vec (shift_right_vec #n (to_vec #n a) s)

(*| Arithmetic right shift by `s` bits: copies of the sign bit are shifted in at the most significant end.

    Total and defined for negative `a`. See `FStar.Int.shift_arithmetic_right_lemma_1` and `FStar.Int.shift_arithmetic_right_lemma_2` for its bits. *)
let shift_arithmetic_right (#n:pos) (a:int_t n) (s:nat) : Tot (int_t n) =
  from_vec (shift_arithmetic_right_vec #n (to_vec #n a) s)

(* Rotate operators *)

(*| Rotates the `n`-bit two's complement representation of `a` left by `s` bits.

    Rotation is at the bit level: the sign bit is rotated like any other bit, so the sign of the result can change. Total, for any `s`; see `FStar.Int.rotate_left_lemma`. *)
let rotate_left (#n:pos) (a:int_t n) (s:nat) : Tot (int_t n) =
  from_vec (rotate_left_vec #n (to_vec #n a) s)

(*| Rotates the `n`-bit two's complement representation of `a` right by `s` bits.

    Rotation is at the bit level: the sign bit is rotated like any other bit, so the sign of the result can change. Total, for any `s`; see `FStar.Int.rotate_right_lemma`. *)
let rotate_right (#n:pos) (a:int_t n) (s:nat) : Tot (int_t n) =
  from_vec (rotate_right_vec #n (to_vec #n a) s)

(* Shift operators lemmas *)
(*| The last `s` bits (indices `i >= n - s`) of `shift_left a s` are unset.

    Triggered automatically on `nth (shift_left a s) i`. *)
val shift_left_lemma_1: #n:pos -> a:int_t n{0 <= a} -> s:nat -> i:nat{i < n && i >= n - s} ->
  Lemma (requires True)
	(ensures (nth (shift_left #n a s) i = false))
	[SMTPat (nth (shift_left #n a s) i)]

(*| Bit `i` of `shift_left a s` is bit `i + s` of `a`, for `i < n - s`.

    Triggered automatically on `nth (shift_left a s) i`. *)
val shift_left_lemma_2: #n:pos -> a:int_t n{0 <= a} -> s:nat -> i:nat{i < n && i < n - s} ->
  Lemma (requires True)
        (ensures (nth (shift_left #n a s) i = nth #n a (i + s)))
	[SMTPat (nth (shift_left #n a s) i)]

(*| The value of a left shift: `shift_left a s = (a * pow2 s) @% pow2 n`, multiplication by `pow2 s` with two's complement wrap-around.

    Triggered automatically on `FStar.Int.shift_left a s`. *)
val shift_left_value_lemma: #n:pos -> a:int_t n{0 <= a} -> s:nat ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) @% pow2 n)
	[SMTPat (shift_left #n a s)]

(*| The first `s` bits (indices `i < s`, the most significant) of `shift_right a s` are unset.

    Triggered automatically on `nth (shift_right a s) i`. *)
val shift_right_lemma_1: #n:pos -> a:int_t n{0 <= a} -> s:nat -> i:nat{i < n && i < s} ->
  Lemma (requires True)
	(ensures (nth (shift_right #n a s) i = false))
	[SMTPat (nth (shift_right #n a s) i)]

(*| Bit `i` of `shift_right a s` is bit `i - s` of `a`, for `i >= s`.

    Triggered automatically on `nth (shift_right a s) i`. *)
val shift_right_lemma_2: #n:pos -> a:int_t n{0 <= a} -> s:nat -> i:nat{i < n && i >= s} ->
  Lemma (requires True)
        (ensures (nth (shift_right #n a s) i = nth #n a (i - s)))
	[SMTPat (nth (shift_right #n a s) i)]

(*| The first `s` bits (indices `i < s`, the most significant) of `shift_arithmetic_right a s` are copies of the sign bit `nth a 0`.

    Triggered automatically on `nth (shift_arithmetic_right a s) i`. *)
val shift_arithmetic_right_lemma_1: #n:pos -> a:int_t n -> s:nat -> i:nat{i < n && i < s} ->
  Lemma (requires True)
	(ensures (nth (shift_arithmetic_right #n a s) i = nth a 0))
	[SMTPat (nth (shift_arithmetic_right #n a s) i)]

(*| Bit `i` of `shift_arithmetic_right a s` is bit `i - s` of `a`, for `i >= s`.

    Triggered automatically on `nth (shift_arithmetic_right a s) i`. *)
val shift_arithmetic_right_lemma_2: #n:pos -> a:int_t n -> s:nat -> i:nat{i < n && i >= s} ->
  Lemma (requires True)
        (ensures (nth (shift_arithmetic_right #n a s) i = nth #n a (i - s)))
	[SMTPat (nth (shift_arithmetic_right #n a s) i)]

(* Rotate operators lemmas *)
(*| Bit `i` of `rotate_left a s` is bit `(i + s) % n` of `a`.

    Triggered automatically on `nth (rotate_left a s) i`. *)
val rotate_left_lemma: #n:pos -> a:int_t n -> s:nat -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (rotate_left #n a s) i = nth #n a ((i + s) % n)))
        [SMTPat (nth (rotate_left #n a s) i)]

(*| Bit `i` of `rotate_right a s` is bit `(i + n - (s % n)) % n` of `a`.

    Triggered automatically on `nth (rotate_right a s) i`. *)
val rotate_right_lemma: #n:pos -> a:int_t n -> s:nat -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (rotate_right #n a s) i = nth #n a ((i + n - (s % n)) % n)))
        [SMTPat (nth (rotate_right #n a s) i)]

(*| Rotating left by the width `n` is the identity.

    Triggered automatically on `rotate_left a n`. *)
val rotate_left_full_identity: #n:pos -> a:int_t n ->
  Lemma (rotate_left #n a n = a)
  [SMTPat (rotate_left #n a n)]

(*| Rotating right by the width `n` is the identity.

    Triggered automatically on `rotate_right a n`. *)
val rotate_right_full_identity: #n:pos -> a:int_t n ->
  Lemma (rotate_right #n a n = a)
  [SMTPat (rotate_right #n a n)]

(*| Rotating left by `s` and then right by `s` gives back the original value. *)
val rotate_left_right_inverse: #n:pos -> a:int_t n -> s:nat ->
  Lemma (rotate_right #n (rotate_left #n a s) s = a)

(*| Rotating right by `s` and then left by `s` gives back the original value. *)
val rotate_right_left_inverse: #n:pos -> a:int_t n -> s:nat ->
  Lemma (rotate_left #n (rotate_right #n a s) s = a)
