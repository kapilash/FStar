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
module FStar.UInt

(* NOTE: anything that you fix/update here should be reflected in [FStar.Int.fsti], which is mostly
 * a copy-paste of this module. *)

open FStar.BitVector
open FStar.Math.Lemmas

(*| Gives the concrete value of `pow2 x` for the common widths `x` in `0`, `1`, `8`, `16`, `31`, `32`, `63`, `64` and `128`.

    For other `x` it states nothing. Triggered automatically on `pow2 x`. *)
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
   | 128 -> p=0x100000000000000000000000000000000
   | _  -> True)
  [SMTPat (pow2 x)]

/// Specs
///
/// Note: lacking any type of functors for F*, this is a copy/paste of [FStar.Int.fst], where the relevant bits that changed are:
///  - definition of max and min
///  - use of regular integer modulus instead of wrap-around modulus

(*| The largest value of an unsigned `n`-bit integer, `pow2 n - 1`. *)
let max_int (n:nat) : Tot int = pow2 n - 1
(*| The smallest value of an unsigned `n`-bit integer, always `0`. *)
let min_int (n:nat) : Tot int = 0

(*| Boolean test that `x` is representable as an unsigned `n`-bit integer, that is `0 <= x <= pow2 n - 1`.

    See also the propositional version `FStar.UInt.size`. *)
let fits (x:int) (n:nat) : Tot bool = min_int n <= x && x <= max_int n
(*| The proposition that `x` is representable as an unsigned `n`-bit integer; `FStar.UInt.fits` as a `prop`.

    This is the refinement of `FStar.UInt.uint_t` and the precondition of the checked operations such as `FStar.UInt.add`. *)
let size (x:int) (n:nat) : prop = fits x n

(* Machine integer type *)
(*| The mathematical model of unsigned `n`-bit integers: the integers `x` with `0 <= x < pow2 n`.

    Machine integer modules such as `FStar.UInt32` and `FStar.UInt64` specify their operations through a value function into `uint_t n`, and the operations here define those specifications. This type is purely mathematical: it is an `int` refinement, so it has no bounded runtime representation of its own. Equality is decidable.

    Its `do_not_unrefine` attribute keeps the experimental `unrefine` mechanism of the unifier (see `Prims.unrefine`) from unfolding it to `int`. *)
[@@do_not_unrefine]
type uint_t (n:nat) = x:int{size x n}

/// Constants

(*| The constant `0` as an unsigned `n`-bit integer. *)
let zero (n:nat) : Tot (uint_t n) = 0

(*| The value `pow2 p` as an unsigned `n`-bit integer, for `p < n`.

    In the big-endian bit numbering of `FStar.UInt.nth`, its only set bit is at index `n - p - 1`. *)
let pow2_n (#n:pos) (p:nat{p < n}) : Tot (uint_t n) =
  pow2_le_compat (n - 1) p; pow2 p

(*| The constant `1` as an unsigned `n`-bit integer, for `n > 0`. *)
let one (n:pos) : Tot (uint_t n) = 1

(*| The unsigned `n`-bit integer with all bits set, equal to `FStar.UInt.max_int n`. *)
let ones (n:nat) : Tot (uint_t n) = max_int n

(* Increment and decrement *)
(*| Adds one; requires `a < max_int n`, so the result never wraps.

    The result is `a + 1` by definition. See `FStar.UInt.incr_mod` for the wrapping variant and `FStar.UInt.incr_underspec` for the abstract one. *)
let incr (#n:nat) (a:uint_t n) : Pure (uint_t n)
  (requires (b2t (a < max_int n))) (ensures (fun _ -> True))
  = a + 1

(*| Subtracts one; requires `a > 0`, so the result never wraps.

    The result is `a - 1` by definition. See `FStar.UInt.decr_mod` for the wrapping variant and `FStar.UInt.decr_underspec` for the abstract one. *)
let decr (#n:nat) (a:uint_t n) : Pure (uint_t n)
  (requires (b2t (a > min_int n))) (ensures (fun _ -> True))
  = a - 1

(*| Abstract increment; requires `a < max_int n` and ensures the result is `a + 1`.

    Unlike `FStar.UInt.incr`, the definition is hidden behind the interface, so only the postcondition is available to proofs. *)
val incr_underspec: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a < max_int n)))
  (ensures (fun b -> a + 1 = b))

(*| Abstract decrement; requires `a > 0` and ensures the result is `a - 1`.

    Unlike `FStar.UInt.decr`, the definition is hidden behind the interface, so only the postcondition is available to proofs. *)
val decr_underspec: #n:nat -> a:uint_t n -> Pure (uint_t n)
  (requires (b2t (a > min_int n)))
  (ensures (fun b -> a - 1 = b))

(*| Increment modulo `pow2 n`: the result is `(a + 1) % pow2 n`, so `max_int n` wraps to `0`. *)
let incr_mod (#n:nat) (a:uint_t n) : Tot (uint_t n) = (a + 1) % (pow2 n)

(*| Decrement modulo `pow2 n`: the result is `(a - 1) % pow2 n`, so `0` wraps to `max_int n`. *)
let decr_mod (#n:nat) (a:uint_t n) : Tot (uint_t n) = (a - 1) % (pow2 n)

(* Addition primitives *)
(*| Checked addition: the result is `a + b`; requires the sum to fit in `n` bits (`size (a + b) n`).

    See `FStar.UInt.add_mod` for wrapping addition and `FStar.UInt.add_underspec` for the variant without a precondition. *)
let add (#n:nat) (a:uint_t n) (b:uint_t n) : Pure (uint_t n)
  (requires (size (a + b) n))
  (ensures (fun _ -> True))
  =  a + b

(*| Addition with no precondition whose result is specified only when there is no overflow.

    If `a + b` fits in `n` bits the result is `a + b`; otherwise the result is an unspecified `n`-bit value. *)
val add_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a + b) n ==> a + b = c))

(*| Wrapping addition: the result is `(a + b) % pow2 n`.

    ```fstar
    let add_mod_wraps () : Lemma (add_mod #8 255 1 == 0) = ()
    ``` *)
let add_mod (#n:nat) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  (a + b) % (pow2 n)

(* Minus primitives *)
(*| Checked subtraction: the result is `a - b`; requires `a - b` to fit in `n` bits, that is `b <= a`.

    See `FStar.UInt.sub_mod` for wrapping subtraction and `FStar.UInt.sub_underspec` for the variant without a precondition. *)
let sub (#n:nat) (a:uint_t n) (b:uint_t n) : Pure (uint_t n)
  (requires (size (a - b) n))
  (ensures (fun _ -> True))
  = a - b

(*| Subtraction with no precondition whose result is specified only when there is no underflow.

    If `a - b` fits in `n` bits the result is `a - b`; otherwise the result is an unspecified `n`-bit value. *)
val sub_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a - b) n ==> a - b = c))

(*| Wrapping subtraction: the result is `(a - b) % pow2 n`, which is `a - b + pow2 n` when `a < b`. *)
let sub_mod (#n:nat) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  (a - b) % (pow2 n)

(* Multiplication primitives *)
(*| Checked multiplication: the result is `a * b`; requires the product to fit in `n` bits.

    See `FStar.UInt.mul_mod` for wrapping multiplication and `FStar.UInt.mul_underspec` for the variant without a precondition. *)
let mul (#n:nat) (a:uint_t n) (b:uint_t n) : Pure (uint_t n)
  (requires (size (a * b) n))
  (ensures (fun _ -> True))
  = a * b

(*| Multiplication with no precondition whose result is specified only when there is no overflow.

    If `a * b` fits in `n` bits the result is `a * b`; otherwise the result is an unspecified `n`-bit value. *)
val mul_underspec: #n:nat -> a:uint_t n -> b:uint_t n -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    size (a * b) n ==> a * b = c))

(*| Wrapping multiplication: the result is `(a * b) % pow2 n`, the low `n` bits of the product. *)
let mul_mod (#n:nat) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  (a * b) % (pow2 n)

private
val lt_square_div_lt (a:nat) (b:pos) : Lemma
  (requires (a < b * b))
  (ensures (a / b < b))

#push-options "--fuel 0 --ifuel 0"
(*| The high half of the full product: the result is `(a * b) / pow2 n`.

    Together with `FStar.UInt.mul_mod` (the low half) it describes the `2n`-bit product of two `n`-bit integers. Total: the quotient always fits in `n` bits. *)
let mul_div (#n:nat) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  FStar.Math.Lemmas.lemma_mult_lt_sqr a b (pow2 n);
  lt_square_div_lt (a * b) (pow2 n);
  (a * b) / (pow2 n)
#pop-options

(* Division primitives *)
(*| Unsigned division: the result is `a / b` (Euclidean division, rounding down); requires `b <> 0`.

    The precondition `size (a / b) n` always holds for unsigned operands (see `FStar.UInt.div_size`). See also `FStar.UInt.udiv`, which has no such precondition. *)
let div (#n:nat) (a:uint_t n) (b:uint_t n{b <> 0}) : Pure (uint_t n)
  (requires (size (a / b) n))
  (ensures (fun c -> b <> 0 ==> a / b = c))
  = a / b

(*| Division with result `a / b` when `b <> 0` and the quotient fits in `n` bits, otherwise unspecified.

    Since the quotient of unsigned operands always fits, this behaves like `FStar.UInt.div`; the definition is hidden behind the interface. *)
val div_underspec: #n:nat -> a:uint_t n -> b:uint_t n{b <> 0} -> Pure (uint_t n)
  (requires True)
  (ensures (fun c ->
    (b <> 0 /\ size (a / b) n) ==> a / b = c))

(*| The quotient `a / b` of two unsigned `n`-bit integers, with `b <> 0`, fits in `n` bits. *)
val div_size: #n:pos -> a:uint_t n -> b:uint_t n{b <> 0} ->
  Lemma (requires (size a n)) (ensures (size (a / b) n))

(*| Total unsigned division: the result is `a / b`, for `b <> 0` and `n > 0`.

    Unlike `FStar.UInt.div`, the bound is discharged internally by `FStar.UInt.div_size`, and the result type carries the equation `a / b = c`. *)
let udiv (#n:pos) (a:uint_t n) (b:uint_t n{b <> 0}) : Tot (c:uint_t n{b <> 0 ==> a / b = c}) =
  div_size #n a b;
  a / b


(* Modulo primitives *)
(*| Unsigned remainder: the result is `a - (a / b) * b`, that is `a % b`; requires `b <> 0`. *)
let mod (#n:nat) (a:uint_t n) (b:uint_t n{b <> 0}) : Tot (uint_t n) =
  a - ((a / b) * b)

(* Comparison operators *)
(*| Boolean equality of two unsigned `n`-bit integers, `a = b`. *)
let eq  #n (a:uint_t n) (b:uint_t n) : Tot bool = (a = b)
(*| Boolean disequality of two unsigned `n`-bit integers, `a <> b`. *)
let ne  #n (a:uint_t n) (b:uint_t n) : Tot bool = (a <> b)
(*| Boolean comparison `a > b` of two unsigned `n`-bit integers. *)
let gt  #n (a:uint_t n) (b:uint_t n) : Tot bool = (a > b)
(*| Boolean comparison `a >= b` of two unsigned `n`-bit integers. *)
let gte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a >= b)
(*| Boolean comparison `a < b` of two unsigned `n`-bit integers. *)
let lt  #n (a:uint_t n) (b:uint_t n) : Tot bool = (a < b)
(*| Boolean comparison `a <= b` of two unsigned `n`-bit integers. *)
let lte #n (a:uint_t n) (b:uint_t n) : Tot bool = (a <= b)

/// Casts

(*| Converts any integer to an unsigned `m`-bit integer by reduction modulo `pow2 m`.

    The result is `a % pow2 m`: values that are too large are truncated to their low `m` bits, and negative values wrap around (two's complement), so `to_uint_t 8 (-1) = 255`.

    ```fstar
    let truncate_cast () : Lemma (to_uint_t 8 300 == 44 /\ to_uint_t 8 (-1) == 255) = ()
    ``` *)
let to_uint_t (m:nat) (a:int) : Tot (uint_t m) = a % pow2 m

open FStar.Seq.Base

(* WARNING: Mind the big endian vs little endian definition *)

(* Casts *)
(*| The `n`-bit vector of an unsigned integer, in big-endian order.

    Index `0` holds the most significant bit and index `n - 1` the least significant bit. The inverse of `FStar.UInt.from_vec`. *)
let rec to_vec (#n:nat) (num:uint_t n) : Tot (bv_t n) =
  if n = 0 then empty #bool
  else append (to_vec #(n - 1) (num / 2)) (create 1 (num % 2 = 1))

(*| The unsigned integer denoted by an `n`-bit vector read in big-endian order.

    Index `0` is the most significant bit. The inverse of `FStar.UInt.to_vec`. *)
let rec from_vec (#n:nat) (vec:bv_t n) : Tot (uint_t n) =
  if n = 0 then 0
  else 2 * from_vec #(n - 1) (slice vec 0 (n - 1)) + (if index vec (n - 1) then 1 else 0)

(*| Equal integers have extensionally equal bit vectors (`FStar.Seq.Base.equal`). *)
val to_vec_lemma_1: #n:nat -> a:uint_t n -> b:uint_t n ->
  Lemma (requires a = b) (ensures equal (to_vec a) (to_vec b))

(*| Integers with extensionally equal bit vectors are equal: `FStar.UInt.to_vec` is injective. *)
val to_vec_lemma_2: #n:nat -> a:uint_t n -> b:uint_t n ->
  Lemma (requires equal (to_vec a) (to_vec b)) (ensures a = b)

(*| Each bit of `to_vec (from_vec vec)` is the corresponding bit of `vec`.

    Triggered automatically on `index (to_vec (from_vec vec)) i`. *)
val inverse_aux: #n:nat -> vec:bv_t n -> i:nat{i < n} ->
  Lemma (requires True) (ensures index vec i = index (to_vec (from_vec vec)) i)
        [SMTPat (index (to_vec (from_vec vec)) i)]

(*| Converting a bit vector to an integer and back gives an extensionally equal vector.

    Triggered automatically on `to_vec (from_vec vec)`. *)
val inverse_vec_lemma: #n:nat -> vec:bv_t n ->
  Lemma (requires True) (ensures equal vec (to_vec (from_vec vec)))
        [SMTPat (to_vec (from_vec vec))]

(*| Converting an integer to a bit vector and back gives the same integer.

    Triggered automatically on `from_vec (to_vec num)`. *)
val inverse_num_lemma: #n:nat -> num:uint_t n ->
  Lemma (requires True) (ensures num = from_vec (to_vec num))
        [SMTPat (from_vec (to_vec num))]

(*| Extensionally equal bit vectors denote the same integer. *)
val from_vec_lemma_1: #n:nat -> a:bv_t n -> b:bv_t n ->
  Lemma (requires equal a b) (ensures from_vec a = from_vec b)

(*| Bit vectors denoting the same integer are extensionally equal: `FStar.UInt.from_vec` is injective. *)
val from_vec_lemma_2: #n:nat -> a:bv_t n -> b:bv_t n ->
  Lemma (requires from_vec a = from_vec b) (ensures equal a b)

(*| An arithmetic regrouping used when splitting a bit vector at two positions `s2 < s1`.

    It states that the value obtained from the three slices `[0, s2)`, `[s2, s1)` and `[s1, n)` can be grouped as the value of the first two slices shifted by `n - s1`, plus the last slice. Mainly a helper for `FStar.UInt.from_vec_propriety`. *)
val from_vec_aux: #n:nat -> a:bv_t n -> s1:nat{s1 < n} -> s2:nat{s2 < s1} ->
  Lemma (requires True)
        (ensures (from_vec #s2 (slice a 0 s2)) * pow2 (n - s2) + (from_vec #(s1 - s2) (slice a s2 s1)) * pow2 (n - s1) + (from_vec #(n - s1) (slice a s1 n)) = ((from_vec #s2 (slice a 0 s2)) * pow2 (s1 - s2) + (from_vec #(s1 - s2) (slice a s2 s1))) * pow2 (n - s1) + (from_vec #(n - s1) (slice a s1 n)))

(*| A slice of a slice is a slice of the original sequence, at the offsets added. *)
val seq_slice_lemma: #n:nat -> a:bv_t n -> s1:nat{s1 < n} -> t1:nat{t1 >= s1 && t1 <= n} -> s2:nat{s2 < t1 - s1} -> t2:nat{t2 >= s2 && t2 <= t1 - s1} ->
  Lemma (equal (slice (slice a s1 t1) s2 t2) (slice a (s1 + s2) (s1 + t2)))

(*| Splitting a bit vector at position `s`: its value is the value of the high part `slice a 0 s` times `pow2 (n - s)`, plus the value of the low part `slice a s n`. *)
val from_vec_propriety: #n:pos -> a:bv_t n -> s:nat{s < n} ->
  Lemma (requires True)
        (ensures from_vec a = (from_vec #s (slice a 0 s)) * pow2 (n - s) + from_vec #(n - s) (slice a s n))
        (decreases (n - s))

(*| The value of the concatenation `append a b` is `from_vec a * pow2 m + from_vec b`, where `m` is the length of `b`. *)
val append_lemma: #n:pos -> #m:pos -> a:bv_t n -> b:bv_t m ->
  Lemma (from_vec #(n + m) (append a b) = (from_vec #n a) * pow2 m + (from_vec #m b))

(*| The leading `s` bits of a vector denote its value divided by `pow2 (n - s)`, that is, its high bits. *)
val slice_left_lemma: #n:pos -> a:bv_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures from_vec #s (slice a 0 s) = (from_vec #n a) / (pow2 (n - s)))

(*| The trailing `s` bits of a vector denote its value modulo `pow2 s`, that is, its low bits. *)
val slice_right_lemma: #n:pos -> a:bv_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures from_vec #s (slice a (n - s) n) = (from_vec #n a) % (pow2 s))

(* Relations between constants in BitVector and in UInt. *)
(*| The bits of `to_vec (zero n)` are those of `FStar.BitVector.zero_vec`, all `false`.

    Triggered automatically on `index (to_vec (zero n)) i`. *)
val zero_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures index (to_vec (zero n)) i = index (zero_vec #n) i)
        [SMTPat (index (to_vec (zero n)) i)]

(*| The all-`false` vector `FStar.BitVector.zero_vec` denotes `zero n`.

    Triggered automatically on `from_vec zero_vec`. *)
val zero_from_vec_lemma: #n:pos ->
  Lemma (requires True) (ensures from_vec (zero_vec #n) = zero n)
        [SMTPat (from_vec (zero_vec #n))]

(*| The bits of `to_vec (one n)` are those of `FStar.BitVector.elem_vec (n - 1)`: only the last, least significant bit is set.

    Triggered automatically on `index (to_vec (one n)) i`. *)
val one_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (one n)) i = index (elem_vec #n (n - 1)) i)
        [SMTPat (index (to_vec (one n)) i)]

(*| The bits of `to_vec (pow2_n p)` are those of `FStar.BitVector.elem_vec (n - p - 1)`.

    Triggered automatically on `index (to_vec (pow2_n p)) i`. *)
val pow2_to_vec_lemma: #n:pos -> p:nat{p < n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (pow2_n #n p)) i = index (elem_vec #n (n - p - 1)) i)
        [SMTPat (index (to_vec (pow2_n #n p)) i)]

(*| The vector `FStar.BitVector.elem_vec p`, with only bit `p` set, denotes `pow2_n (n - p - 1)`.

    Triggered automatically on `from_vec (elem_vec p)`. *)
val pow2_from_vec_lemma: #n:pos -> p:nat{p < n} ->
  Lemma (requires True) (ensures from_vec (elem_vec #n p) = pow2_n #n (n - p - 1))
        [SMTPat (from_vec (elem_vec #n p))]

(*| The bits of `to_vec (ones n)` are those of `FStar.BitVector.ones_vec`, all `true`.

    Triggered automatically on `index (to_vec (ones n)) i`. *)
val ones_to_vec_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures index (to_vec (ones n)) i = index (ones_vec #n) i)
        [SMTPat (index (to_vec (ones n)) i)]

(*| The all-`true` vector `FStar.BitVector.ones_vec` denotes `ones n`.

    Triggered automatically on `from_vec ones_vec`. *)
val ones_from_vec_lemma: #n:pos ->
  Lemma (requires True) (ensures from_vec (ones_vec #n) = ones n)
        [SMTPat (from_vec (ones_vec #n))]


(* (nth a i) returns a boolean indicating the i-th bit of a. *)
(*| Bit `i` of `a`, counted in big-endian order: `nth a 0` is the most significant bit and `nth a (n - 1)` the least significant.

    Defined as `index (to_vec a) i`. The bitwise operations are specified bit by bit with `nth`. *)
let nth (#n:pos) (a:uint_t n) (i:nat{i < n}) : Tot bool =
  index (to_vec #n a) i

(*| Bit extensionality: two `n`-bit integers that agree on every bit are equal.

    ```fstar
    let same_bits (#n: pos) (a b: uint_t n)
      : Lemma (requires forall (i: nat{i < n}). nth a i = nth b i)
              (ensures a == b)
      = nth_lemma a b
    ``` *)
val nth_lemma: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires forall (i:nat{i < n}). nth a i = nth b i)
        (ensures a = b)

(* Lemmas for constants *)
(*| Every bit of `zero n` is `false`.

    Triggered automatically on `nth (zero n) i`. *)
val zero_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures nth (zero n) i = false)
        [SMTPat (nth (zero n) i)]

(*| The only set bit of `pow2_n p` is at index `n - p - 1`.

    Triggered automatically on `nth (pow2_n p) i`. *)
val pow2_nth_lemma: #n:pos -> p:nat{p < n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (i = n - p - 1 ==> nth (pow2_n #n p) i = true) /\
                 (i <> n - p - 1 ==> nth (pow2_n #n p) i = false))
        [SMTPat (nth (pow2_n #n p) i)]

(*| The only set bit of `one n` is the least significant one, at index `n - 1`.

    Triggered automatically on `nth (one n) i`. *)
val one_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (i = n - 1 ==> nth (one n) i = true) /\
                 (i < n - 1 ==> nth (one n) i = false))
        [SMTPat (nth (one n) i)]

(*| Every bit of `ones n` is `true`.

    Triggered automatically on `nth (ones n) i`. *)
val ones_nth_lemma: #n:pos -> i:nat{i < n} ->
  Lemma (requires True) (ensures (nth (ones n) i) = true)
        [SMTPat (nth (ones n) i)]

(* Bitwise operators *)
(*| Bitwise AND of two unsigned `n`-bit integers.

    Specified bit by bit by `FStar.UInt.logand_definition`. *)
let logand (#n:pos) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  from_vec #n (logand_vec #n (to_vec #n a) (to_vec #n b))

(*| Bitwise exclusive OR of two unsigned `n`-bit integers.

    Specified bit by bit by `FStar.UInt.logxor_definition`. *)
let logxor (#n:pos) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  from_vec #n (logxor_vec #n (to_vec #n a) (to_vec #n b))

(*| Bitwise inclusive OR of two unsigned `n`-bit integers.

    Specified bit by bit by `FStar.UInt.logor_definition`. *)
let logor (#n:pos) (a:uint_t n) (b:uint_t n) : Tot (uint_t n) =
  from_vec #n (logor_vec #n (to_vec #n a) (to_vec #n b))

(*| Bitwise complement of an unsigned `n`-bit integer.

    Its value is `pow2 n - a - 1` (see `FStar.UInt.lemma_lognot_value_mod`). *)
let lognot (#n:pos) (a:uint_t n) : Tot (uint_t n) =
  from_vec #n (lognot_vec #n (to_vec #n a))

(* Bitwise operators definitions *)
(*| Bit `i` of `logand a b` is the conjunction of bit `i` of `a` and of `b`.

    Triggered automatically on `nth (logand a b) i`. *)
val logand_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (logand a b) i = (nth a i && nth b i)))
        [SMTPat (nth (logand a b) i)]

(*| Bit `i` of `logxor a b` is `true` exactly when bits `i` of `a` and `b` differ.

    Triggered automatically on `nth (logxor a b) i`. *)
val logxor_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (logxor a b) i = (nth a i <> nth b i)))
        [SMTPat (nth (logxor a b) i)]

(*| Bit `i` of `logor a b` is the disjunction of bit `i` of `a` and of `b`.

    Triggered automatically on `nth (logor a b) i`. *)
val logor_definition: #n:pos -> a:uint_t n -> b:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (logor a b) i = (nth a i || nth b i)))
        [SMTPat (nth (logor a b) i)]

(*| Bit `i` of `lognot a` is the negation of bit `i` of `a`.

    Triggered automatically on `nth (lognot a) i`. *)
val lognot_definition: #n:pos -> a:uint_t n -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (lognot a) i = not(nth a i)))
        [SMTPat (nth (lognot a) i)]

(* Two's complement unary minus *)
(*| Two's complement negation modulo `pow2 n`: `add_mod (lognot a) 1`.

    The result equals `sub_mod 0 a`, that is `(0 - a) % pow2 n` (see `FStar.UInt.lemma_minus_eq_zero_sub`); `minus 0 = 0`. *)
inline_for_extraction
let minus (#n:pos) (a:uint_t n) : Tot (uint_t n) =
  add_mod (lognot a) 1

(* Bitwise operators lemmas *)
(* TODO: lemmas about the relations between different operators *)
(* Bitwise AND operator *)
(*| Bitwise AND is commutative. *)
val logand_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logand #n a b = logand #n b a))

(*| Bitwise AND is associative. *)
val logand_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True)
        (ensures (logand #n (logand #n a b) c = logand #n a (logand #n b c)))

(*| Bitwise AND is idempotent: `logand a a = a`. *)
val logand_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logand #n a a = a))

(*| Zero absorbs bitwise AND: `logand a (zero n) = zero n`. *)
val logand_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logand #n a (zero n) = zero n))

(*| All-ones is the identity of bitwise AND: `logand a (ones n) = a`. *)
val logand_lemma_2: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logand #n a (ones n) = a))

(* subset_vec_le_lemma proves that a subset of bits is numerically smaller or equal. *)
(*| A bit vector whose set bits are a subset of those of another (`FStar.BitVector.is_subset_vec`) denotes a smaller or equal number. *)
val subset_vec_le_lemma: #n:pos -> a:bv_t n -> b:bv_t n ->
  Lemma (requires is_subset_vec #n a b) (ensures (from_vec a) <= (from_vec b))

(* logand_le proves the the result of AND is less than or equal to both arguments. *)
(*| The bitwise AND of two integers is at most each of them. *)
val logand_le: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True)
        (ensures (logand a b) <= a /\ (logand a b) <= b)

(* Bitwise XOR operator *)
(*| Bitwise XOR is commutative. *)
val logxor_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a b = logxor #n b a))

(*| Bitwise XOR is associative. *)
val logxor_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True) (ensures (logxor #n (logxor #n a b) c = logxor #n a (logxor #n b c)))

(*| The bitwise XOR of a value with itself is zero. *)
val logxor_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a a = zero n))

(*| Zero is the identity of bitwise XOR: `logxor a (zero n) = a`. *)
val logxor_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a (zero n) = a))

(*| XOR with all-ones is complement: `logxor a (ones n) = lognot a`. *)
val logxor_lemma_2: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logxor #n a (ones n) = lognot #n a))

private let xor (b:bool) (b':bool) : Tot bool = b <> b'

private val xor_lemma (a:bool) (b:bool) : Lemma
  (requires (True))
  (ensures  (xor (xor a b) b = a))
  [SMTPat (xor (xor a b) b)]

(*| XOR with the same value twice cancels: `logxor (logxor a b) b = a`. *)
val logxor_inv: #n:pos -> a:uint_t n -> b:uint_t n -> Lemma
  (a = logxor #n (logxor #n a b) b)

(*| The bitwise XOR of two distinct values is nonzero. *)
val logxor_neq_nonzero: #n:pos -> a:uint_t n -> b:uint_t n -> Lemma
   (a <> b ==> logxor a b <> 0)

(* Bitwise OR operators *)
(*| Bitwise OR is commutative. *)
val logor_commutative: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True) (ensures (logor #n a b = logor #n b a))

(*| Bitwise OR is associative. *)
val logor_associative: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
  Lemma (requires True)
        (ensures (logor #n (logor #n a b) c = logor #n a (logor #n b c)))

(*| Bitwise OR is idempotent: `logor a a = a`. *)
val logor_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logor #n a a = a))

(*| Zero is the identity of bitwise OR: `logor a (zero n) = a`. *)
val logor_lemma_1: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logor #n a (zero n) = a))

(*| All-ones absorbs bitwise OR: `logor a (ones n) = ones n`. *)
val logor_lemma_2: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (logor #n a (ones n) = ones n))


(* superset_vec_le_lemma proves that a superset of bits is numerically greater than or equal. *)
(*| A bit vector whose set bits are a superset of those of another (`FStar.BitVector.is_superset_vec`) denotes a greater or equal number. *)
val superset_vec_ge_lemma: #n:pos -> a:bv_t n -> b:bv_t n ->
  Lemma (requires is_superset_vec #n a b)
        (ensures (from_vec a) >= (from_vec b))

(* logor_ge proves that the result of an OR is greater than or equal to both arguments. *)
(*| The bitwise OR of two integers is at least each of them. *)
val logor_ge: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (requires True)
        (ensures (logor a b) >= a /\ (logor a b) >= b)

(* Bitwise NOT operator *)
(*| Complement is an involution: `lognot (lognot a) = a`. *)
val lognot_self: #n:pos -> a:uint_t n ->
  Lemma (requires True) (ensures (lognot #n (lognot #n a) = a))

(*| The complement of zero is all-ones: `lognot (zero n) = ones n`. *)
val lognot_lemma_1: #n:pos ->
  Lemma (requires True) (ensures (lognot #n (zero n) = ones n))

(** Used in the next two lemmas *)
private val index_to_vec_ones: #n:pos -> m:nat{m <= n} -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (pow2 m <= pow2 n /\
          (i < n - m ==> index (to_vec #n (pow2 m - 1)) i == false) /\
          (n - m <= i ==> index (to_vec #n (pow2 m - 1)) i == true)))
        [SMTPat (index (to_vec #n (pow2 m - 1)) i)]


(*| OR of values with disjoint bits is addition: if `a` is a multiple of `pow2 m` and `b < pow2 m`, then `logor a b == a + b`.

    Requires `0 < m < n`. *)
val logor_disjoint: #n:pos -> a:uint_t n -> b:uint_t n -> m:pos{m < n} ->
  Lemma (requires (a % pow2 m == 0 /\ b < pow2 m))
        (ensures  (logor #n a b == a + b))

(*| Masking with `pow2 m - 1` keeps the low `m` bits: `logand a (pow2 m - 1) == a % pow2 m`, for `0 < m < n`.

    ```fstar
    let low_bits (a: uint_t 32)
      : Lemma (logand #32 a 0xff == a % 256)
      = logand_mask #32 a 8
    ``` *)
val logand_mask: #n:pos -> a:uint_t n -> m:pos{m < n} ->
  Lemma (pow2 m < pow2 n /\ logand #n a (pow2 m - 1) == a % pow2 m)


(* Shift operators *)

(*| Logical left shift by `s` bits; vacated low bits are filled with zeros and high bits are discarded.

    Its value is `(a * pow2 s) % pow2 n` (`FStar.UInt.shift_left_value_lemma`), which is `0` when `s >= n`. Any `s` is allowed.

    ```fstar
    let shift_is_mul (a: uint_t 32)
      : Lemma (shift_left #32 a 4 == (a * pow2 4) % pow2 32)
      = ()
    ``` *)
let shift_left (#n:pos) (a:uint_t n) (s:nat) : Tot (uint_t n) =
  from_vec (shift_left_vec #n (to_vec #n a) s)

(*| Logical right shift by `s` bits; vacated high bits are filled with zeros.

    Its value is `a / pow2 s` (`FStar.UInt.shift_right_value_lemma`), which is `0` when `s >= n`. Any `s` is allowed. *)
let shift_right (#n:pos) (a:uint_t n) (s:nat) : Tot (uint_t n) =
  from_vec (shift_right_vec #n (to_vec #n a) s)

(* Rotate operators *)

(*| Rotates the bits of `a` left (towards the most significant end) by `s` positions; bits leaving at the top re-enter at the bottom.

    The amount is taken modulo `n`. See `FStar.UInt.rotate_left_lemma`. *)
let rotate_left (#n:pos) (a:uint_t n) (s:nat) : Tot (uint_t n) =
  from_vec (rotate_left_vec #n (to_vec #n a) s)

(*| Rotates the bits of `a` right (towards the least significant end) by `s` positions; bits leaving at the bottom re-enter at the top.

    The amount is taken modulo `n`. See `FStar.UInt.rotate_right_lemma`. *)
let rotate_right (#n:pos) (a:uint_t n) (s:nat) : Tot (uint_t n) =
  from_vec (rotate_right_vec #n (to_vec #n a) s)

(* Shift operators lemmas *)
(*| The low `s` bits of `shift_left a s`, at indices `i >= n - s`, are zero.

    Triggered automatically on `nth (shift_left a s) i`. *)
val shift_left_lemma_1: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i >= n - s} ->
  Lemma (requires True)
        (ensures (nth (shift_left #n a s) i = false))
        [SMTPat (nth (shift_left #n a s) i)]

(*| For `i < n - s`, bit `i` of `shift_left a s` is bit `i + s` of `a`.

    Triggered automatically on `nth (shift_left a s) i`. *)
val shift_left_lemma_2: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i < n - s} ->
  Lemma (requires True)
        (ensures (nth (shift_left #n a s) i = nth #n a (i + s)))
        [SMTPat (nth (shift_left #n a s) i)]

(*| The high `s` bits of `shift_right a s`, at indices `i < s`, are zero.

    Triggered automatically on `nth (shift_right a s) i`. *)
val shift_right_lemma_1: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i < s} ->
  Lemma (requires True)
        (ensures (nth (shift_right #n a s) i = false))
        [SMTPat (nth (shift_right #n a s) i)]

(*| For `i >= s`, bit `i` of `shift_right a s` is bit `i - s` of `a`.

    Triggered automatically on `nth (shift_right a s) i`. *)
val shift_right_lemma_2: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n && i >= s} ->
  Lemma (requires True)
        (ensures (nth (shift_right #n a s) i = nth #n a (i - s)))
        [SMTPat (nth (shift_right #n a s) i)]

(* Lemmas with shift operators and bitwise operators *)
(*| Left shift distributes over bitwise AND. *)
val shift_left_logand_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logand #n a b) s = logand #n (shift_left #n a s) (shift_left #n b s)))

(*| Right shift distributes over bitwise AND. *)
val shift_right_logand_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logand #n a b) s = logand #n (shift_right #n a s) (shift_right #n b s)))

(*| Left shift distributes over bitwise XOR. *)
val shift_left_logxor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logxor #n a b) s = logxor #n (shift_left #n a s) (shift_left #n b s)))

(*| Right shift distributes over bitwise XOR. *)
val shift_right_logxor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logxor #n a b) s = logxor #n (shift_right #n a s) (shift_right #n b s)))

(*| Left shift distributes over bitwise OR. *)
val shift_left_logor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_left #n (logor #n a b) s = logor #n (shift_left #n a s) (shift_left #n b s)))

(*| Right shift distributes over bitwise OR. *)
val shift_right_logor_lemma: #n:pos -> a:uint_t n -> b:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures (shift_right #n (logor #n a b) s = logor #n (shift_right #n a s) (shift_right #n b s)))

(* Rotate operators lemmas *)

(*| Bit `i` of `rotate_left a s` is bit `(i + s) % n` of `a`.

    Triggered automatically on `nth (rotate_left a s) i`. *)
val rotate_left_lemma: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (rotate_left #n a s) i = nth #n a ((i + s) % n)))
        [SMTPat (nth (rotate_left #n a s) i)]

(*| Bit `i` of `rotate_right a s` is bit `(i + n - s % n) % n` of `a`.

    Unlike `FStar.UInt.rotate_left_lemma`, it has no SMT pattern and must be called explicitly. *)
val rotate_right_lemma: #n:pos -> a:uint_t n -> s:nat -> i:nat{i < n} ->
  Lemma (requires True)
        (ensures (nth (rotate_right #n a s) i = nth #n a ((i + n - (s % n)) % n)))

(*| Rotating left by the full width `n` is the identity.

    Triggered automatically on `rotate_left a n`. *)
val rotate_left_full_identity: #n:pos -> a:uint_t n ->
  Lemma (rotate_left #n a n = a)
  [SMTPat (rotate_left #n a n)]

(*| Rotating right by the full width `n` is the identity.

    Triggered automatically on `rotate_right a n`. *)
val rotate_right_full_identity: #n:pos -> a:uint_t n ->
  Lemma (rotate_right #n a n = a)
  [SMTPat (rotate_right #n a n)]

(*| Rotating left then right by the same amount gives back the original value. *)
val rotate_left_right_inverse: #n:pos -> a:uint_t n -> s:nat ->
  Lemma (rotate_right #n (rotate_left #n a s) s = a)

(*| Rotating right then left by the same amount gives back the original value. *)
val rotate_right_left_inverse: #n:pos -> a:uint_t n -> s:nat ->
  Lemma (rotate_left #n (rotate_right #n a s) s = a)


(* Lemmas about value after shift operations *)
(*| The value of `shift_left a s` is `(a * pow2 s) % pow2 n`, in the case `s >= n` (where both sides are `0`).

    A case of `FStar.UInt.shift_left_value_lemma`, which covers all `s`. *)
val shift_left_value_aux_1: #n:pos -> a:uint_t n -> s:nat{s >= n} ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)

(*| The value of `shift_left a 0` is `(a * pow2 0) % pow2 n`, that is `a`.

    A case of `FStar.UInt.shift_left_value_lemma`, which covers all `s`. *)
val shift_left_value_aux_2: #n:pos -> a:uint_t n ->
  Lemma (requires True)
        (ensures shift_left #n a 0 = (a * pow2 0) % pow2 n)

(*| The value of `shift_left a s` is `(a * pow2 s) % pow2 n`, in the case `0 < s < n`.

    A case of `FStar.UInt.shift_left_value_lemma`, which covers all `s`. *)
val shift_left_value_aux_3: #n:pos -> a:uint_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)

(*| The value of a left shift: `shift_left a s = (a * pow2 s) % pow2 n`.

    Triggered automatically on `shift_left a s`. *)
val shift_left_value_lemma: #n:pos -> a:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures shift_left #n a s = (a * pow2 s) % pow2 n)
        [SMTPat (shift_left #n a s)]

(*| The value of `shift_right a s` is `a / pow2 s`, in the case `s >= n` (where both sides are `0`).

    A case of `FStar.UInt.shift_right_value_lemma`, which covers all `s`. *)
val shift_right_value_aux_1: #n:pos -> a:uint_t n -> s:nat{s >= n} ->
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)

(*| The value of `shift_right a 0` is `a / pow2 0`, that is `a`.

    A case of `FStar.UInt.shift_right_value_lemma`, which covers all `s`. *)
val shift_right_value_aux_2: #n:pos -> a:uint_t n ->
  Lemma (requires True)
        (ensures shift_right #n a 0 = a / pow2 0)

(*| The value of `shift_right a s` is `a / pow2 s`, in the case `0 < s < n`.

    A case of `FStar.UInt.shift_right_value_lemma`, which covers all `s`. *)
val shift_right_value_aux_3: #n:pos -> a:uint_t n -> s:pos{s < n} ->
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)

(*| The value of a right shift: `shift_right a s = a / pow2 s`.

    Triggered automatically on `shift_right a s`. *)
val shift_right_value_lemma: #n:pos -> a:uint_t n -> s:nat ->
  Lemma (requires True)
        (ensures shift_right #n a s = a / pow2 s)
        [SMTPat (shift_right #n a s)]

(* Lemmas about the most significant bit in various situations *)

(*| The most significant bit of `a`, `nth a 0`.

    It is set exactly when `a >= pow2 (n - 1)` (`FStar.UInt.lemma_msb_pow2`). *)
let msb (#n:pos) (a:uint_t n) : Tot bool = nth a 0

(*| The most significant bit is set exactly when `a >= pow2 (n - 1)`. *)
val lemma_msb_pow2: #n:pos -> a:uint_t n ->
  Lemma (msb a <==> a >= pow2 (n-1))

(*| The two's complement negation `FStar.UInt.minus a` is zero only when `a` is zero. *)
val lemma_minus_zero: #n:pos -> a:uint_t n ->
  Lemma (minus a = 0 ==> a = 0)

(*| If `a >= b` and the most significant bit of `a` is clear, then so is that of `b`.

    Requires `n > 1`. *)
val lemma_msb_gte: #n:pos{n > 1} -> a:uint_t n -> b:uint_t n ->
  Lemma ((a >= b && not (msb a)) ==> not (msb b))


(* Lemmas toward showing ~n + 1 = -a *)

(*| An unsigned `n`-bit integer is unchanged by reduction modulo `pow2 n`. *)
val lemma_uint_mod: #n:pos -> a:uint_t n ->
  Lemma (a = a % pow2 n)

(*| Wrapping subtraction then addition of `b` cancel: `add_mod (sub_mod a b) b = a`. *)
val lemma_add_sub_cancel: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (add_mod (sub_mod a b) b = a)

(*| Reducing the left operand of a subtraction modulo `p` does not change the result modulo `p`: `(a - b) % p = ((a % p) - b) % p`.

    A general integer lemma, not specific to `uint_t`. *)
val lemma_mod_sub_distr_l: a:int -> b:int -> p:pos ->
  Lemma ((a - b) % p = ((a % p) - b) % p)

(*| Wrapping addition then subtraction of `b` cancel: `sub_mod (add_mod a b) b = a`. *)
val lemma_sub_add_cancel: #n:pos -> a:uint_t n -> b:uint_t n ->
  Lemma (sub_mod (add_mod a b) b = a)

(*| Extends an `n`-bit vector to `n + 1` bits by prepending a `false` (most significant) bit. *)
let zero_extend_vec (#n:pos) (a:BitVector.bv_t n): Tot (BitVector.bv_t (n+1)) = append (create 1 false) a
(*| Extends an `n`-bit vector to `n + m` bits by prepending `m` `false` (most significant) bits. *)
let zero_extends_vec (#n:pos) (m: pos) (a:BitVector.bv_t n): Tot (BitVector.bv_t (n+m)) = append (zero_vec #m) a
(*| Extends an `n`-bit vector to `n + 1` bits by prepending a `true` (most significant) bit. *)
let one_extend_vec (#n:pos) (a:BitVector.bv_t n): Tot (BitVector.bv_t (n+1)) = append (create 1 true) a

(*| Widens an unsigned `n`-bit integer to `n + 1` bits by adding a zero most significant bit; the value is unchanged.

    See `FStar.UInt.lemma_zero_extend`. *)
let zero_extend (#n:pos) (a:uint_t n): Tot (uint_t (n+1)) = from_vec (zero_extend_vec (to_vec a))
(*| Widens an unsigned `n`-bit integer to `n + m` bits by adding `m` zero most significant bits; the value is unchanged.

    See `FStar.UInt.lemma_zero_extends`. *)
let zero_extends (#n:pos) (m: pos) (a:uint_t n): Tot (uint_t (n+m)) = from_vec (zero_extends_vec m (to_vec a))
(*| Widens an unsigned `n`-bit integer to `n + 1` bits by adding a one most significant bit; the value becomes `pow2 n + a`.

    See `FStar.UInt.lemma_one_extend`. *)
let one_extend (#n:pos) (a:uint_t n): Tot (uint_t (n+1)) = from_vec (one_extend_vec (to_vec a))

(*| Zero extension preserves the value: `zero_extend a = a`.

    Triggered automatically on `zero_extend a`. *)
val lemma_zero_extend: #n:pos -> a:uint_t n ->
  Lemma (zero_extend a = a)
  [SMTPat (zero_extend a)]

(*| Zero extension by `m` bits preserves the value: `zero_extends m a = a`.

    Triggered automatically on `zero_extends m a`. *)
val lemma_zero_extends: #n:pos -> m: pos -> a:uint_t n ->
  Lemma (zero_extends #n m a = a)
  [SMTPat (zero_extends #n m a)]

(*| One extension adds `pow2 n`: `one_extend a = pow2 n + a`.

    Triggered automatically on `one_extend a`. *)
val lemma_one_extend: #n:pos -> a:uint_t n ->
  Lemma (one_extend a = pow2 n + a)
  [SMTPat (one_extend a)]

(*| The `n + 1`-bit complement of a zero-extended value is `pow2 n` plus the `n`-bit complement. *)
val lemma_lognot_zero_ext: #n:pos -> a:uint_t n ->
  Lemma (lognot #(n+1) (zero_extend a) = pow2 n + (lognot #n a))

(*| The `n + 1`-bit complement of a one-extended value equals the `n`-bit complement. *)
val lemma_lognot_one_ext: #n:pos -> a:uint_t n ->
  Lemma (lognot #(n+1) (one_extend a) = lognot #n a)

(*| The value of the complement: `lognot a = pow2 n - a - 1`. *)
val lemma_lognot_value_mod: #n:pos -> a:uint_t n ->
  Lemma
  (requires True)
  (ensures (lognot a = pow2 n - a - 1))
  (decreases n)

(*| The case `a = 0` of `FStar.UInt.lemma_lognot_value`. *)
val lemma_lognot_value_zero: #n:pos -> a:uint_t n{a = 0} ->
  Lemma (lognot a = sub_mod (sub_mod 0 a) 1)

(*| `1 % pow2 n = 1` for `n > 0`. *)
val lemma_one_mod_pow2: #n:pos ->
  Lemma (1 = 1 % (pow2 n))

(*| The case `a <> 0` of `FStar.UInt.lemma_lognot_value`. *)
val lemma_lognot_value_nonzero: #n:pos -> a:uint_t n{a <> 0} ->
  Lemma (lognot a = sub_mod (sub_mod 0 a) 1)

(*| The complement in terms of wrapping subtraction: `lognot a = sub_mod (sub_mod 0 a) 1`, that is, `-a - 1` modulo `pow2 n`. *)
val lemma_lognot_value: #n:pos -> a:uint_t n ->
  Lemma (lognot #n a = sub_mod (sub_mod 0 a) 1)

(*| Two's complement negation is wrapping subtraction from zero: `minus a = sub_mod 0 a`. *)
val lemma_minus_eq_zero_sub: #n:pos -> a:uint_t n ->
  Lemma (minus #n a = sub_mod #n 0 a)
