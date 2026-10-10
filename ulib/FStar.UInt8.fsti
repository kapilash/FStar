(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.UInt8

(**** THIS MODULE IS GENERATED AUTOMATICALLY USING [mk_int.sh], DO NOT EDIT DIRECTLY ****)

(*| The bit width of `t`.

    Values of `t` range from `0` to `pow2 n - 1`. *)
unfold let n = 8

/// For FStar.UIntN.fstp: anything that you fix/update here should be
/// reflected in [FStar.IntN.fstp], which is mostly a copy-paste of
/// this module.
///
/// Except, as compared to [FStar.IntN.fstp], here:
///  - every occurrence of [int_t] has been replaced with [uint_t]
///  - every occurrence of [@%] has been replaced with [%].
///  - some functions (e.g., add_underspec, etc.) are only defined here, not on signed integers

/// This module provides an abstract type for machine integers of a
/// given signedness and width. The interface is designed to be safe
/// with respect to arithmetic underflow and overflow.

/// Note, we have attempted several times to re-design this module to
/// make it more amenable to normalization and to impose less overhead
/// on the SMT solver when reasoning about machine integer
/// arithmetic. The following github issue reports on the current
/// status of that work.
///
/// https://github.com/FStarLang/FStar/issues/1757

open FStar.UInt

(*| Abstract type of unsigned `n`-bit machine integers.

    The value of `x : t` is `v x`, a mathematical integer in `FStar.UInt.uint_t n`, that is between `0` and `pow2 n - 1`; every operation of this module is specified through `v`. Equality is decidable, and the polymorphic `=` agrees with `eq`. Code extraction treats this type and its operations as machine integer primitives; their behaviour is assumed to match this `v`-based model. *)
new val t : eqtype

(*| The value of a machine integer, as a mathematical integer in `FStar.UInt.uint_t n`.

    This is the specification model of all operations of this module. Its inverse is `uint_to_t`. *)
val v (x:t) : Tot (uint_t n)

(*| The proposition that `x` is representable as an unsigned `n`-bit integer, that is `0 <= x <= pow2 n - 1`.

    It is `FStar.UInt.fits x n` as a `prop`. *)
let fits (x:int) : prop = UInt.fits x n

(*| Converts a mathematical integer in `FStar.UInt.uint_t n` to a machine integer, with `v (uint_to_t x) == x`.

    The argument must already be in range; this is enforced by its type, not by wrapping. Integer literals with the type's suffix are desugared to this conversion, with the range check done when desugaring. *)
val uint_to_t (x:uint_t n) : Pure t
  (requires True)
  (ensures (fun y -> v y = x))

(*| Converting a machine integer to its value and back is the identity: `uint_to_t (v x) == x`.

    Triggered automatically on `v x`. *)
val uv_inv (x : t) : Lemma
  (ensures (uint_to_t (v x) == x))
  [SMTPat (v x)]

(*| Converting an in-range mathematical integer to a machine integer and back is the identity: `v (uint_to_t x) == x`.

    Triggered automatically on `uint_to_t x`. *)
val vu_inv (x : uint_t n) : Lemma
  (ensures (v (uint_to_t x) == x))
  [SMTPat (uint_to_t x)]

(*| The value function `v` is injective: machine integers with equal values are equal.

    It has no SMT pattern; call it to conclude `x1 == x2` from `v x1 == v x2`. *)
val v_inj (x1 x2: t): Lemma
  (requires (v x1 == v x2))
  (ensures (x1 == x2))

(*| The machine integer with value `0`. *)
val zero : x:t{v x = 0}

(*| The machine integer with value `1`. *)
val one : x:t{v x = 1}

(**** Addition primitives *)

(*| Addition that cannot overflow: `v (add a b) == v a + v b`; requires the sum to fit in `n` bits.

    The precondition is `FStar.UInt.size (v a + v b) n`. Infix form `+`. See `add_mod` for wrapping addition and `add_underspec` for addition without a precondition. *)
val add (a:t) (b:t) : Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))

(*| Addition that may overflow, with a result specified only when it does not.

    If the sum fits in `n` bits, `v (add_underspec a b) == v a + v b`; otherwise the result is an unspecified value of type `t`. No precondition. Infix form `+?^`. See `add_mod` for the wrapping semantics. *)
val add_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a + v b) n ==> v a + v b = v c))

(*| Wrapping addition: `v (add_mod a b) == (v a + v b) % pow2 n`.

    Total; specified by `FStar.UInt.add_mod`. Infix form `+%^`. See `add` for addition that must not overflow. *)
val add_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.add_mod (v a) (v b) = v c))

(**** Minus primitives *)


(*| Subtraction that cannot underflow: `v (sub a b) == v a - v b`; requires `v b <= v a`.

    The precondition is `FStar.UInt.size (v a - v b) n`. Infix form `-`. See `sub_mod` for wrapping subtraction and `sub_underspec` for subtraction without a precondition. *)
val sub (a:t) (b:t) : Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))

(*| Subtraction that may underflow, with a result specified only when it does not.

    If `v a - v b` fits in `n` bits (that is `v b <= v a`), `v (sub_underspec a b) == v a - v b`; otherwise the result is an unspecified value of type `t`. No precondition. Infix form `-?^`. *)
val sub_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a - v b) n ==> v a - v b = v c))

(*| Wrapping subtraction: `v (sub_mod a b) == (v a - v b) % pow2 n`.

    Total; specified by `FStar.UInt.sub_mod`, so the result is `v a - v b + pow2 n` when `v a < v b`. Infix form `-%^`. *)
val sub_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.sub_mod (v a) (v b) = v c))

(**** Multiplication primitives *)


(*| Multiplication that cannot overflow: `v (mul a b) == v a * v b`; requires the product to fit in `n` bits.

    The precondition is `FStar.UInt.size (v a * v b) n`. Infix form `*`. See `mul_mod` for wrapping multiplication and `mul_underspec` for multiplication without a precondition. *)
val mul (a:t) (b:t) : Pure t
  (requires (size (v a * v b) n))
  (ensures (fun c -> v a * v b = v c))

(*| Multiplication that may overflow, with a result specified only when it does not.

    If the product fits in `n` bits, `v (mul_underspec a b) == v a * v b`; otherwise the result is an unspecified value of type `t`. No precondition. Infix form `*?^`. *)
val mul_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a * v b) n ==> v a * v b = v c))

(*| Wrapping multiplication: `v (mul_mod a b) == (v a * v b) % pow2 n`.

    Total; specified by `FStar.UInt.mul_mod`. Infix form `*%^`. *)
val mul_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.mul_mod (v a) (v b) = v c))

(**** Division primitives *)

(*| Unsigned division rounding down: `v (div a b) == v a / v b`; the divisor must be nonzero.

    The nonzero divisor is required by the refinement on `b`; the quotient always fits, so there is no overflow. Infix form `/`. *)
val div (a:t) (b:t{v b <> 0}) : Pure t
  (requires (True))
  (ensures (fun c -> v a / v b = v c))

(**** Modulo primitives *)

(*| Remainder of unsigned division: `v (rem a b) == v a % v b`; the divisor must be nonzero.

    Specified by `FStar.UInt.mod`. Infix form `%`. *)
val rem (a:t) (b:t{v b <> 0}) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.mod (v a) (v b) = v c))

(**** Bitwise operators *)

/// Also see FStar.BV

(*| Bitwise AND: `v (logand x y) == FStar.UInt.logand (v x) (v y)`.

    Total. Infix form `&^`. *)
val logand (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logand` v y = v z))

(*| Bitwise exclusive OR: `v (logxor x y) == FStar.UInt.logxor (v x) (v y)`.

    Total. Infix form `^^`. *)
val logxor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logxor` v y == v z))

(*| Bitwise OR: `v (logor x y) == FStar.UInt.logor (v x) (v y)`.

    Total. Infix form `|^`. *)
val logor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logor` v y == v z))

(*| Bitwise complement: `v (lognot x) == FStar.UInt.lognot (v x)`.

    Total. Its value is `pow2 n - 1 - v x` (see `FStar.UInt.lemma_lognot_value`). *)
val lognot (x:t) : Pure t
  (requires True)
  (ensures (fun z -> lognot (v x) == v z))

(**** Shift operators *)

(*| Logical right shift by `s` bits, filling with zeros: `v (shift_right a s) == FStar.UInt.shift_right (v a) k`, where `k` is the value of `s`.

    The shift amount `s` is a 32-bit unsigned integer whose value `k` must be strictly less than `n`. The value is `v a / pow2 k` (see `FStar.UInt.shift_right_value_lemma`). Infix form `>>^`. *)
val shift_right (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.UInt.shift_right (v a) (UInt32.v s) = v c))

(*| Left shift by `s` bits, filling with zeros: `v (shift_left a s) == FStar.UInt.shift_left (v a) k`, where `k` is the value of `s`.

    The shift amount `s` is a 32-bit unsigned integer whose value `k` must be strictly less than `n`. Bits shifted out are lost: the value is `(v a * pow2 k) % pow2 n` (see `FStar.UInt.shift_left_value_lemma`). Infix form `<<^`. *)
val shift_left (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.UInt.shift_left (v a) (UInt32.v s) = v c))

(**** Rotate operators *)

(*| Rotates the `n` bits of `a` right by `s` positions: `v (rotate_right a s) == FStar.UInt.rotate_right (v a) k`, where `k` is the value of `s`.

    The rotation amount `s` is a 32-bit unsigned integer whose value `k` must be strictly less than `n`. Infix form `>>>^`. *)
val rotate_right (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.UInt.rotate_right (v a) (UInt32.v s) = v c))

(*| Rotates the `n` bits of `a` left by `s` positions: `v (rotate_left a s) == FStar.UInt.rotate_left (v a) k`, where `k` is the value of `s`.

    The rotation amount `s` is a 32-bit unsigned integer whose value `k` must be strictly less than `n`. Infix form `<<<^`. *)
val rotate_left (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.UInt.rotate_left (v a) (UInt32.v s) = v c))

(**** Comparison operators *)

(*| Boolean equality of machine integers: `eq a b = (v a = v b)`.

    The polymorphic decidable equality `a = b` gives the same result. Infix form `=^`. *)
let eq (a:t) (b:t) : Tot bool = eq #n (v a) (v b)

(*| Boolean disequality of machine integers: `ne a b = (v a <> v b)`.

    Infix form `<>^`. *)
let ne (a:t) (b:t) : Tot bool = ne #n (v a) (v b)

(*| Unsigned comparison `v a > v b`, as a boolean.

    Infix form `>`. *)
let gt (a:t) (b:t) : Tot bool = gt #n (v a) (v b)

(*| Unsigned comparison `v a >= v b`, as a boolean.

    Infix form `>=`. *)
let gte (a:t) (b:t) : Tot bool = gte #n (v a) (v b)

(*| Unsigned comparison `v a < v b`, as a boolean.

    Infix form `<`. *)
let lt (a:t) (b:t) : Tot bool = lt #n (v a) (v b)

(*| Unsigned comparison `v a <= v b`, as a boolean.

    Infix form `<=`. *)
let lte (a:t) (b:t) : Tot bool = lte #n (v a) (v b)

(*| Two's complement negation modulo `pow2 n`, defined as `add_mod (lognot a) (uint_to_t 1)`.

    Total; its value is `(pow2 n - v a) % pow2 n`, so `minus` of zero is zero. *)
inline_for_extraction
let minus (a:t) = add_mod (lognot a) (uint_to_t 1)

(*| The width minus one, `n - 1`, as a 32-bit unsigned integer.

    This is the largest shift or rotation amount accepted by `shift_left`, `shift_right`, `rotate_left` and `rotate_right`. *)
inline_for_extraction
let n_minus_one = UInt32.uint_to_t (n - 1)

#push-options "--fuel 1"
(*| Equality mask for constant-time code: all bits set (`pow2 n - 1`) when `v a = v b`, and `0` otherwise.

    Total. The result is computed with `logxor`, `minus`, `logor`, `shift_right` and `sub_mod`; the `if` on `a = b` in its definition only selects proof steps. The specification only states the value, not timing behaviour. The `CNoInline` attribute asks C extraction not to inline it. Adapted from [a WireGuard commit](https://git.zx2c4.com/WireGuard/commit/src/crypto/curve25519-hacl64.h?id=2e60bb395c1f589a398ec606d611132ef9ef764b). *)
[@ CNoInline ]
let eq_mask (a:t) (b:t)
  : Pure t
    (requires True)
    (ensures (fun c -> (v a = v b ==> v c = pow2 n - 1) /\
                       (v a <> v b ==> v c = 0)))
  = let x = logxor a b in
    let minus_x = minus x in
    let x_or_minus_x = logor x minus_x in
    let xnx = shift_right x_or_minus_x n_minus_one in
    let c = sub_mod xnx (uint_to_t 1) in
    if a = b then
    begin
      logxor_self (v a);
      lognot_lemma_1 #n;
      logor_lemma_1 (v x);
      assert (v x = 0 /\ v minus_x = 0 /\
              v x_or_minus_x = 0 /\ v xnx = 0);
      assert (v c = ones n)
    end
    else
    begin
      logxor_neq_nonzero (v a) (v b);
      lemma_msb_pow2 #n (v (lognot x));
      lemma_msb_pow2 #n (v minus_x);
      lemma_minus_zero #n (v x);
      assert (v c = FStar.UInt.zero n)
    end;
    c

private
val lemma_sub_msbs (a:t) (b:t)
    : Lemma ((msb (v a) = msb (v b)) ==> (v a < v b <==> msb (v (sub_mod a b))))

(*| Unsigned comparison mask for constant-time code: all bits set (`pow2 n - 1`) when `v a >= v b`, and `0` otherwise.

    Total. The result is computed with bitwise operations, `sub_mod` and `shift_right`, without branching. The specification only states the value, not timing behaviour. The `CNoInline` attribute asks C extraction not to inline it. Adapted from [a WireGuard commit](https://git.zx2c4.com/WireGuard/commit/src/crypto/curve25519-hacl64.h?id=0a483a9b431d87eca1b275463c632f8d5551978a). *)
[@ CNoInline ]
let gte_mask (a:t) (b:t)
  : Pure t
    (requires True)
    (ensures (fun c -> (v a >= v b ==> v c = pow2 n - 1) /\
                       (v a < v b ==> v c = 0)))
  = let x = a in
    let y = b in
    let x_xor_y = logxor x y in
    let x_sub_y = sub_mod x y in
    let x_sub_y_xor_y = logxor x_sub_y y in
    let q = logor x_xor_y x_sub_y_xor_y in
    let x_xor_q = logxor x q in
    let x_xor_q_ = shift_right x_xor_q n_minus_one in
    let c = sub_mod x_xor_q_ (uint_to_t 1) in
    lemma_sub_msbs x y;
    lemma_msb_gte (v x) (v y);
    lemma_msb_gte (v y) (v x);
    c
#pop-options

(*** Infix notations *)
(*| Infix notation for `add`: addition that requires the sum to fit in `n` bits. *)
inline_for_extraction unfold let ( + )  = add
(*| Infix notation for `add_underspec`: addition whose result is unspecified on overflow. *)
inline_for_extraction unfold let ( +?^ ) = add_underspec
(*| Infix notation for `add_mod`: addition modulo `pow2 n`. *)
inline_for_extraction unfold let ( +%^ ) = add_mod
(*| Infix notation for `sub`: subtraction that requires the difference to be nonnegative. *)
inline_for_extraction unfold let ( - )  = sub
(*| Infix notation for `sub_underspec`: subtraction whose result is unspecified on underflow. *)
inline_for_extraction unfold let ( -?^ ) = sub_underspec
(*| Infix notation for `sub_mod`: subtraction modulo `pow2 n`. *)
inline_for_extraction unfold let ( -%^ ) = sub_mod
(*| Infix notation for `mul`: multiplication that requires the product to fit in `n` bits. *)
inline_for_extraction unfold let ( * ) = mul
(*| Infix notation for `mul_underspec`: multiplication whose result is unspecified on overflow. *)
inline_for_extraction unfold let ( *?^ )= mul_underspec
(*| Infix notation for `mul_mod`: multiplication modulo `pow2 n`. *)
inline_for_extraction unfold let ( *%^ )= mul_mod
(*| Infix notation for `div`: unsigned division by a nonzero divisor. *)
inline_for_extraction unfold let ( / )  = div
(*| Infix notation for `rem`: unsigned remainder by a nonzero divisor. *)
inline_for_extraction unfold let ( % )  = rem
(*| Infix notation for `logxor`: bitwise exclusive OR. *)
inline_for_extraction unfold let ( ^^ )  = logxor
(*| Infix notation for `logand`: bitwise AND. *)
inline_for_extraction unfold let ( &^ )  = logand
(*| Infix notation for `logor`: bitwise OR. *)
inline_for_extraction unfold let ( |^ )  = logor
(*| Infix notation for `shift_left`: left shift by fewer than `n` bits. *)
inline_for_extraction unfold let ( <<^ ) = shift_left
(*| Infix notation for `shift_right`: logical right shift by fewer than `n` bits. *)
inline_for_extraction unfold let ( >>^ ) = shift_right
(*| Infix notation for `rotate_left`: left rotation by fewer than `n` bits. *)
inline_for_extraction unfold let ( <<<^ ) = rotate_left
(*| Infix notation for `rotate_right`: right rotation by fewer than `n` bits. *)
inline_for_extraction unfold let ( >>>^ ) = rotate_right
(*| Infix notation for `eq`: boolean equality. *)
inline_for_extraction unfold let ( =^ )  = eq
(*| Infix notation for `ne`: boolean disequality. *)
inline_for_extraction unfold let ( <>^ ) = ne
(*| Infix notation for `gt`: unsigned greater-than test. *)
inline_for_extraction unfold let ( > )  = gt
(*| Infix notation for `gte`: unsigned greater-than-or-equal test. *)
inline_for_extraction unfold let ( >= ) = gte
(*| Infix notation for `lt`: unsigned less-than test. *)
inline_for_extraction unfold let ( < )  = lt
(*| Infix notation for `lte`: unsigned less-than-or-equal test. *)
inline_for_extraction unfold let ( <= ) = lte

(*** Deprecated infix notations

The nine operators above used to carry a [^] suffix, to keep them apart from
the ones on [int] and from those of the other widths. Type-based overloading
now tells them apart, so they are spelled without the suffix. The old spellings
remain, deprecated, so that code written against the earlier library keeps
checking. *)
(*| Deprecated spelling of `+` (that is `add`); use `+`. *)
[@@deprecated "use ( + )"]  inline_for_extraction unfold let ( +^ )  = add
(*| Deprecated spelling of `-` (that is `sub`); use `-`. *)
[@@deprecated "use ( - )"]  inline_for_extraction unfold let ( -^ )  = sub
(*| Deprecated spelling of `*` (that is `mul`); use `*`. *)
[@@deprecated "use ( * )"]  inline_for_extraction unfold let ( *^ )  = mul
(*| Deprecated spelling of `/` (that is `div`); use `/`. *)
[@@deprecated "use ( / )"]  inline_for_extraction unfold let ( /^ )  = div
(*| Deprecated spelling of `%` (that is `rem`); use `%`. *)
[@@deprecated "use ( % )"]  inline_for_extraction unfold let ( %^ )  = rem
(*| Deprecated spelling of `>` (that is `gt`); use `>`. *)
[@@deprecated "use ( > )"]  inline_for_extraction unfold let ( >^ )  = gt
(*| Deprecated spelling of `>=` (that is `gte`); use `>=`. *)
[@@deprecated "use ( >= )"] inline_for_extraction unfold let ( >=^ ) = gte
(*| Deprecated spelling of `<` (that is `lt`); use `<`. *)
[@@deprecated "use ( < )"]  inline_for_extraction unfold let ( <^ )  = lt
(*| Deprecated spelling of `<=` (that is `lte`); use `<=`. *)
[@@deprecated "use ( <= )"] inline_for_extraction unfold let ( <=^ ) = lte

(**** To input / output constants *)
(*| Renders a machine integer as a decimal string.

    Total, but it has no logical specification: its definition in the implementation is admitted and the behaviour is provided by the extraction runtime. *)
val to_string: t -> Tot string

(*| Renders a machine integer as a hexadecimal string with a leading `0x`.

    Total, but it has no logical specification: its definition in the implementation is admitted and the behaviour is provided by the extraction runtime. *)
val to_string_hex: t -> Tot string

(*| Renders a machine integer as a fixed-width hexadecimal string, left-padded with zeros to the full width of the type, without a leading `0x`.

    Total, but it has no logical specification: its definition in the implementation is admitted and the behaviour is provided by the extraction runtime. *)
val to_string_hex_pad: t -> Tot string

(*| Parses a machine integer from its string representation.

    Total, but it has no logical specification: its definition in the implementation is admitted and the behaviour, including on strings that are not a valid in-range literal, is left to the extraction runtime. Nothing can be proved about its result. *)
val of_string: string -> Tot t

//This private primitive is used internally by the
//compiler to translate bounded integer constants
//with a desugaring-time check of the size of the number,
//rather than an expensive verification check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
[@@admitted]
private
unfold
let __uint_to_t (x:int) : t =
  uint_to_t x

(*| An abbreviation for `t`, the unsigned 8-bit machine integer type, conventionally used for bytes. *)
unfold inline_for_extraction type byte = t
