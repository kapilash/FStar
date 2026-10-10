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
module FStar.Int64

(**** THIS MODULE IS GENERATED AUTOMATICALLY USING [mk_int.sh], DO NOT EDIT DIRECTLY ****)

(*| The bit width of `t`.

    Values of `t` are two's complement integers ranging from `FStar.Int.min_int n` to `FStar.Int.max_int n`. *)
unfold let n = 64

open FStar.Int

(* NOTE: anything that you fix/update here should be reflected in [FStar.UIntN.fstp], which is mostly
 * a copy-paste of this module. *)

(*| Abstract type of signed `n`-bit machine integers.

    The value of `x : t` is `v x`, a mathematical integer in `FStar.Int.int_t n`, that is between `FStar.Int.min_int n` (`-pow2 (n - 1)`) and `FStar.Int.max_int n` (`pow2 (n - 1) - 1`); every operation of this module is specified through `v`. Equality is decidable, and the polymorphic `=` agrees with `eq`. Code extraction treats this type and its operations as machine integer primitives; their behaviour is assumed to match this `v`-based model. *)
new val t : eqtype

(*| The value of a machine integer, as a mathematical integer in `FStar.Int.int_t n`.

    This is the specification model of all operations of this module. Its inverse is `int_to_t`. *)
val v (x:t) : Tot (int_t n)

(*| The proposition that `x` is representable as a signed `n`-bit integer, that is `FStar.Int.min_int n <= x <= FStar.Int.max_int n`.

    It is `FStar.Int.fits x n` as a `prop`. *)
let fits (x:int) : prop = Int.fits x n

(*| Converts a mathematical integer in `FStar.Int.int_t n` to a machine integer, with `v (int_to_t x) == x`.

    The argument must already be in range; this is enforced by its type, not by wrapping. Integer literals with the type's suffix are desugared to this conversion, with the range check done when desugaring. *)
val int_to_t: x:int_t n -> Pure t
  (requires True)
  (ensures (fun y -> v y = x))

(*| Converting a machine integer to its value and back is the identity: `int_to_t (v x) == x`.

    Triggered automatically on `v x`. *)
val uv_inv (x : t) : Lemma
  (ensures (int_to_t (v x) == x))
  [SMTPat (v x)]

(*| Converting an in-range mathematical integer to a machine integer and back is the identity: `v (int_to_t x) == x`.

    Triggered automatically on `int_to_t x`. *)
val vu_inv (x : int_t n) : Lemma
  (ensures (v (int_to_t x) == x))
  [SMTPat (int_to_t x)]

(*| The value function `v` is injective: machine integers with equal values are equal.

    It has no SMT pattern; call it to conclude `x1 == x2` from `v x1 == v x2`. *)
val v_inj (x1 x2: t): Lemma
  (requires (v x1 == v x2))
  (ensures (x1 == x2))

(*| The machine integer with value `0`. *)
val zero : x:t{v x = 0}

(*| The machine integer with value `1`. *)
val one : x:t{v x = 1}

(*| Addition that cannot overflow: `v (add a b) == v a + v b`; requires the sum to fit in `n` bits.

    The precondition is `FStar.Int.size (v a + v b) n`. Infix form `+`. Signed machine integers have no wrapping or underspecified variants in this module; `FStar.Int.add_mod` gives the wrapping semantics on the mathematical model. *)
val add (a:t) (b:t) : Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))

(* Minus primitives *)
(*| Subtraction that cannot overflow: `v (sub a b) == v a - v b`; requires the difference to fit in `n` bits.

    The precondition is `FStar.Int.size (v a - v b) n`. Infix form `-`. *)
val sub (a:t) (b:t) : Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))

(* Multiplication primitives *)
(*| Multiplication that cannot overflow: `v (mul a b) == v a * v b`; requires the product to fit in `n` bits.

    The precondition is `FStar.Int.size (v a * v b) n`. Infix form `*`. *)
val mul (a:t) (b:t) : Pure t
  (requires (size (v a * v b) n))
  (ensures (fun c -> v a * v b = v c))

(* Division primitives. Note division truncates towards zero (/-). *)
(*| Signed division truncating towards zero, as in C: `v (div a b) == v a /- v b`, using the `/-` operator of `FStar.Int`.

    The divisor must be nonzero (refinement on `b`) and the quotient must fit in `n` bits, which excludes only `FStar.Int.min_int n` divided by `-1`. This is not the Euclidean division `/` on `int`: the quotient of `-7` by `2` is `-3`. Infix form `/`. *)
val div (a:t) (b:t{v b <> 0}) : Pure t
  // division overflows on INT_MIN / -1
  (requires (size (v a /- v b) n))
  (ensures (fun c -> v a /- v b = v c))

(* Modulo primitives *)
(*| Signed remainder of truncating division, as the C `%` operator: `v (rem a b) == FStar.Int.mod (v a) (v b)`, that is `v a - (v a /- v b) * v b`.

    The result has the sign of the dividend `a` (or is zero), so this is not the Euclidean modulo: the remainder of `-7` by `2` is `-1`. The divisor must be nonzero and, as for `div`, the quotient `v a /- v b` must fit in `n` bits, which excludes `FStar.Int.min_int n` with divisor `-1`. Infix form `%`. *)
val rem (a:t) (b:t{v b <> 0}) : Pure t
  (requires (size (v a /- v b) n))
  (ensures (fun c -> FStar.Int.mod (v a) (v b) = v c))

(* Bitwise operators *)
(*| Bitwise AND of the two's complement representations: `v (logand x y) == FStar.Int.logand (v x) (v y)`.

    Total. Infix form `&^`. *)
val logand (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logand` v y = v z))

(*| Bitwise exclusive OR of the two's complement representations: `v (logxor x y) == FStar.Int.logxor (v x) (v y)`.

    Total. Infix form `^^`. *)
val logxor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logxor` v y == v z))

(*| Bitwise OR of the two's complement representations: `v (logor x y) == FStar.Int.logor (v x) (v y)`.

    Total. Infix form `|^`. *)
val logor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logor` v y == v z))

(*| Bitwise complement of the two's complement representation: `v (lognot x) == FStar.Int.lognot (v x)`.

    Total. Characterized bit by bit by `FStar.Int.lognot_definition`; see `FStar.Int.lognot_negative` for its value on negative arguments. *)
val lognot (x:t) : Pure t
  (requires True)
  (ensures (fun z -> lognot (v x) == v z))

(* Shift operators *)

(*| Logical right shift of a nonnegative integer by `s` bits: `v (shift_right a s) == FStar.Int.shift_right (v a) k`, where `k` is the value of `s`.

    Requires `0 <= v a` and `k < n`, where the shift amount `s` is a 32-bit unsigned integer. Since `a` is nonnegative, zeros are shifted in. For negative values use `shift_arithmetic_right`. Infix form `>>^`. *)
val shift_right (a:t) (s:UInt32.t) : Pure t
  (requires (0 <= v a /\ UInt32.v s < n))
  (ensures (fun c -> FStar.Int.shift_right (v a) (UInt32.v s) = v c))

(*| Left shift of a nonnegative integer by `s` bits, without overflow: `v (shift_left a s) == FStar.Int.shift_left (v a) k`, where `k` is the value of `s`.

    Requires `0 <= v a`, `v a * pow2 k <= FStar.Int.max_int n` and `k < n`, where the shift amount `s` is a 32-bit unsigned integer. Under these conditions the value is `v a * pow2 k` (see `FStar.Int.shift_left_value_lemma`). Infix form `<<^`. *)
val shift_left (a:t) (s:UInt32.t) : Pure t
  (requires (0 <= v a /\ v a * pow2 (UInt32.v s) <= max_int n /\ UInt32.v s < n))
  (ensures (fun c -> FStar.Int.shift_left (v a) (UInt32.v s) = v c))

(*| Arithmetic right shift by `s` bits, shifting in copies of the sign bit: `v (shift_arithmetic_right a s) == FStar.Int.shift_arithmetic_right (v a) k`, where `k` is the value of `s`.

    Defined for negative `a`. The shift amount `s` is a 32-bit unsigned integer whose value `k` must be strictly less than `n`. Infix form `>>>^` (unlike the unsigned modules, where `>>>^` is a rotation). *)
val shift_arithmetic_right (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.Int.shift_arithmetic_right (v a) (UInt32.v s) = v c))

(* Rotate operators *)

(*| Rotates the `n`-bit two's complement representation of `a` right by `s` positions: `v (rotate_right a s) == FStar.Int.rotate_right (v a) k`, where `k` is the value of `s`.

    Rotation is at the bit level and essentially unsigned: the sign bit is rotated like any other bit. The rotation amount `s` is a 32-bit unsigned integer whose value `k` must be strictly less than `n`. There is no infix form. *)
val rotate_right (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.Int.rotate_right (v a) (UInt32.v s) = v c))

(*| Rotates the `n`-bit two's complement representation of `a` left by `s` positions: `v (rotate_left a s) == FStar.Int.rotate_left (v a) k`, where `k` is the value of `s`.

    Rotation is at the bit level and essentially unsigned: the sign bit is rotated like any other bit. The rotation amount `s` is a 32-bit unsigned integer whose value `k` must be strictly less than `n`. There is no infix form. *)
val rotate_left (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.Int.rotate_left (v a) (UInt32.v s) = v c))

(* Comparison operators *)
(*| Boolean equality of machine integers: `eq a b = (v a = v b)`.

    The polymorphic decidable equality `a = b` gives the same result. Infix form `=^`. *)
let eq  (a:t) (b:t) : Tot bool = eq  #n (v a) (v b)
(*| Boolean disequality of machine integers: `ne a b = (v a <> v b)`.

    Infix form `<>^`. *)
let ne  (a:t) (b:t) : Tot bool = ne  #n (v a) (v b)
(*| Signed comparison `v a > v b`, as a boolean.

    Infix form `>`. *)
let gt  (a:t) (b:t) : Tot bool = gt  #n (v a) (v b)
(*| Signed comparison `v a >= v b`, as a boolean.

    Infix form `>=`. *)
let gte (a:t) (b:t) : Tot bool = gte #n (v a) (v b)
(*| Signed comparison `v a < v b`, as a boolean.

    Infix form `<`. *)
let lt ( a:t) (b:t) : Tot bool = lt  #n (v a) (v b)
(*| Signed comparison `v a <= v b`, as a boolean.

    Infix form `<=`. *)
let lte (a:t) (b:t) : Tot bool = lte #n (v a) (v b)


#push-options "--fuel 0 --ifuel 0"
(*| Absolute value computed without branching on the value: `v (ct_abs a) == abs (v a)`; requires `v a > FStar.Int.min_int n`.

    The minimum value is excluded because its absolute value does not fit in `n` bits. The result is `sub (logxor a mask) mask`, where `mask` is `a` shifted arithmetically right by `n - 1` bits; the `if` in its definition only selects proof steps. The specification only states the value, not timing behaviour. *)
inline_for_extraction
let ct_abs (a:t{min_int n < v a}) : Tot (b:t{v b = abs (v a)}) =
  let mask = shift_arithmetic_right a (UInt32.uint_to_t (n - 1)) in
  if 0 <= v a then
    begin
    sign_bit_positive (v a);
    nth_lemma (v mask) (FStar.Int.zero _);
    logxor_lemma_1 (v a)
    end
  else
    begin
    sign_bit_negative (v a);
    nth_lemma (v mask) (ones _);
    logxor_lemma_2 (v a);
    lognot_negative (v a);
    UInt.lemma_lognot_value #n (to_uint (v a))
    end;
  sub (logxor a mask) mask
#pop-options

(* Infix notations *)
(*| Infix notation for `add`: addition that requires the sum to fit in `n` bits. *)
inline_for_extraction unfold let ( + )  = add
(*| Infix notation for `sub`: subtraction that requires the difference to fit in `n` bits. *)
inline_for_extraction unfold let ( - )  = sub
(*| Infix notation for `mul`: multiplication that requires the product to fit in `n` bits. *)
inline_for_extraction unfold let ( * )  = mul
(*| Infix notation for `div`: signed division truncating towards zero. *)
inline_for_extraction unfold let ( / )  = div
(*| Infix notation for `rem`: signed remainder, with the sign of the dividend. *)
inline_for_extraction unfold let ( % )  = rem
(*| Infix notation for `logxor`: bitwise exclusive OR. *)
inline_for_extraction unfold let ( ^^ )  = logxor
(*| Infix notation for `logand`: bitwise AND. *)
inline_for_extraction unfold let ( &^ )  = logand
(*| Infix notation for `logor`: bitwise OR. *)
inline_for_extraction unfold let ( |^ )  = logor
(*| Infix notation for `shift_left`: left shift of a nonnegative integer, without overflow. *)
inline_for_extraction unfold let ( <<^ ) = shift_left
(*| Infix notation for `shift_right`: logical right shift of a nonnegative integer. *)
inline_for_extraction unfold let ( >>^ ) = shift_right
(*| Infix notation for `shift_arithmetic_right`: arithmetic right shift, defined for negative values. *)
inline_for_extraction unfold let ( >>>^) = shift_arithmetic_right
(*| Infix notation for `eq`: boolean equality. *)
inline_for_extraction unfold let ( =^ )  = eq
(*| Infix notation for `ne`: boolean disequality. *)
inline_for_extraction unfold let ( <>^ ) = ne
(*| Infix notation for `gt`: signed greater-than test. *)
inline_for_extraction unfold let ( > )  = gt
(*| Infix notation for `gte`: signed greater-than-or-equal test. *)
inline_for_extraction unfold let ( >= ) = gte
(*| Infix notation for `lt`: signed less-than test. *)
inline_for_extraction unfold let ( < )  = lt
(*| Infix notation for `lte`: signed less-than-or-equal test. *)
inline_for_extraction unfold let ( <= ) = lte

(* Deprecated infix notations

   The nine operators above used to carry a [^] suffix, to keep them apart from
   the ones on [int] and from those of the other widths. Type-based overloading
   now tells them apart, so they are spelled without the suffix. The old
   spellings remain, deprecated, so that code written against the earlier
   library keeps checking. *)
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

(* To input / output constants *)
(* .. in decimal representation *)
(*| Renders a machine integer as a decimal string.

    Total, but it has no logical specification: its definition in the implementation is admitted and the behaviour is provided by the extraction runtime. *)
val to_string: t -> Tot string

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
let __int_to_t (x:int) : t =
  int_to_t x
