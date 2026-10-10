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
module FStar.UInt128

open FStar.UInt

module U32 = FStar.UInt32
module U64 = FStar.UInt64

(*| The bit width of `FStar.UInt128.t`, namely `128`. *)
noextract
let n = 128

(*| The type of unsigned 128-bit machine integers, with decidable equality.

    `t` is abstract; its values correspond exactly to `FStar.UInt.uint_t 128`
    through `FStar.UInt128.v` and `FStar.UInt128.uint_to_t`. The F\*
    implementation represents a value as a pair of 64-bit halves; clients
    can only observe it through `v`.

    Unlike `FStar.UInt64`, this module offers no full 128-bit multiplication,
    division or remainder; see `FStar.UInt128.mul_wide` and
    `FStar.UInt128.mul32` for widening products. *)
val t: (x:Type0{hasEq x})

(*| The mathematical value of a 128-bit integer, as a `FStar.UInt.uint_t 128`.

    Total; marked `noextract_to "krml"`, so it is meant for specifications
    and must not appear in code extracted to C. *)
[@@ noextract_to "krml"]
val v (x:t) : Tot (uint_t n)

(*| Builds a 128-bit integer from its value, with `v (uint_to_t x) = x`.

    The argument must be in `FStar.UInt.uint_t 128`, that is `0 <= x < pow2 128`.
    Marked `noextract_to "krml"`. *)
[@@ noextract_to "krml"]
val uint_to_t: x:uint_t n -> Pure t
  (requires True)
  (ensures (fun y -> v y = x))

(*| `FStar.UInt128.v` is injective: two integers with the same value are
    equal.

    Not an SMT pattern; call it explicitly. *)
val v_inj (x1 x2: t): Lemma (requires (v x1 == v x2)) (ensures (x1 == x2))

(*| Addition without overflow: `v (add a b) == v a + v b`.

    Requires the sum to fit in 128 bits (`FStar.UInt.size (v a + v b) 128`).
    See `FStar.UInt128.add_mod` for wrapping and
    `FStar.UInt128.add_underspec` for an unchecked variant. Infix:
    `FStar.UInt128.op_Plus`. *)
val add: a:t -> b:t -> Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))

(*| Addition with no precondition whose result is only specified when it does
    not overflow.

    If `v a + v b` fits in 128 bits the result has that value; otherwise the
    result is an unspecified 128-bit integer. Infix:
    `FStar.UInt128.op_Plus_Question_Hat`. *)
val add_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    size (v a + v b) n ==> v a + v b = v c))

(*| Wrapping addition: `v (add_mod a b) == (v a + v b) % pow2 128`.

    No precondition. Infix: `FStar.UInt128.op_Plus_Percent_Hat`.

    ```fstar
    let incr_wraps (x: FStar.UInt128.t)
      : Lemma (FStar.UInt128.v (FStar.UInt128.add_mod x (FStar.UInt128.uint_to_t 1))
               == (FStar.UInt128.v x + 1) % pow2 128)
      = ()
    ``` *)
val add_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a + v b) % pow2 n = v c))

(* Minus primitives *)
(*| Subtraction without underflow: `v (sub a b) == v a - v b`.

    Requires `v a - v b` to fit in 128 bits, that is `v b <= v a`. See
    `FStar.UInt128.sub_mod` for wrapping and `FStar.UInt128.sub_underspec`
    for an unchecked variant. Infix: `FStar.UInt128.op_Minus`. *)
val sub: a:t -> b:t -> Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))

(*| Subtraction with no precondition whose result is only specified when it
    does not underflow.

    If `v b <= v a` the result is `v a - v b`; otherwise the result is an
    unspecified 128-bit integer. Infix: `FStar.UInt128.op_Minus_Question_Hat`. *)
val sub_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    size (v a - v b) n ==> v a - v b = v c))

(*| Wrapping subtraction: `v (sub_mod a b) == (v a - v b) % pow2 128`.

    No precondition. Infix: `FStar.UInt128.op_Minus_Percent_Hat`. *)
val sub_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a - v b) % pow2 n = v c))

(* Bitwise operators *)
(*| Bitwise and, specified by `FStar.UInt.logand` on the values. Infix:
    `FStar.UInt128.op_Amp_Hat`. *)
val logand: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun r -> v r == logand (v a) (v b)))

(*| Bitwise exclusive or, specified by `FStar.UInt.logxor` on the values.
    Infix: `FStar.UInt128.op_Hat_Hat`. *)
val logxor: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun r -> v r == logxor (v a) (v b)))

(*| Bitwise or, specified by `FStar.UInt.logor` on the values. Infix:
    `FStar.UInt128.op_Bar_Hat`. *)
val logor: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun r -> v r == logor (v a) (v b)))

(*| Bitwise complement, specified by `FStar.UInt.lognot` on the value; that
    is `pow2 128 - 1 - v a`. There is no infix notation. *)
val lognot: a:t -> Pure t
  (requires True)
  (ensures (fun r -> v r == lognot (v a)))

//This private primitive is used internally by the
//compiler to translate bounded integer constants
//with a desugaring-time check of the size of the number,
//rather than an expensive verifiation check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
private
unfold
let __uint_to_t (x:int) : Tot t =
      assume (fits x 128);
      uint_to_t x


(* Shift operators *)
(*| Logical left shift: `v (shift_left a s) == (v a * pow2 (v s)) % pow2 128`.

    Bits shifted out are lost. Requires the shift amount `s`, a
    `FStar.UInt32.t`, to be below 128. Infix:
    `FStar.UInt128.op_Less_Less_Hat`. *)
val shift_left: a:t -> s:UInt32.t -> Pure t
  (requires (U32.v s < n))
  (ensures (fun c -> v c = ((v a * pow2 (UInt32.v s)) % pow2 n)))

(*| Logical right shift: `v (shift_right a s) == v a / pow2 (v s)`.

    Requires the shift amount `s`, a `FStar.UInt32.t`, to be below 128.
    Infix: `FStar.UInt128.op_Greater_Greater_Hat`. *)
val shift_right: a:t -> s:UInt32.t -> Pure t
  (requires (U32.v s < n))
  (ensures (fun c -> v c = (v a / (pow2 (UInt32.v s)))))

(* Comparison operators *)

(*| Equality test, returning `v a = v b`. Infix:
    `FStar.UInt128.op_Equals_Hat`. *)
val eq (a:t) (b:t) : Pure bool
  (requires True)
  (ensures (fun r -> r == eq #n (v a) (v b)))

(*| Strict greater-than test, returning `v a > v b`. Infix:
    `FStar.UInt128.op_Greater`. *)
val gt (a:t) (b:t) : Pure bool
  (requires True)
  (ensures (fun r -> r == gt #n (v a) (v b)))

(*| Strict less-than test, returning `v a < v b`. Infix:
    `FStar.UInt128.op_Less`. *)
val lt (a:t) (b:t) : Pure bool
  (requires True)
  (ensures (fun r -> r == lt #n (v a) (v b)))

(*| Greater-than-or-equal test, returning `v a >= v b`. Infix:
    `FStar.UInt128.op_Greater_Equals`. *)
val gte (a:t) (b:t) : Pure bool
  (requires True)
  (ensures (fun r -> r == gte #n (v a) (v b)))

(*| Less-than-or-equal test, returning `v a <= v b`. Infix:
    `FStar.UInt128.op_Less_Equals`. *)
val lte (a:t) (b:t) : Pure bool
  (requires True)
  (ensures (fun r -> r == lte #n (v a) (v b)))

(*| Equality as a mask: all ones (`pow2 128 - 1`) when `v a = v b`, and `0`
    otherwise.

    The specification says nothing about timing behaviour. *)
val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b ==> v c = pow2 n - 1) /\ (v a <> v b ==> v c = 0)})

(*| Comparison as a mask: all ones (`pow2 128 - 1`) when `v a >= v b`, and
    `0` otherwise.

    The specification says nothing about timing behaviour. *)
val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b ==> v c = pow2 n - 1) /\ (v a < v b ==> v c = 0)})

(* Casts *)
(*| Widens a 64-bit unsigned integer to 128 bits, preserving its value. *)
val uint64_to_uint128: a:U64.t -> b:t{v b == U64.v a}
(*| Truncates a 128-bit integer to its low 64 bits: the result has value
    `v a % pow2 64`.

    ```fstar
    let low_half (x: FStar.UInt128.t)
      : r:FStar.UInt64.t{FStar.UInt64.v r == FStar.UInt128.v x % pow2 64}
      = FStar.UInt128.uint128_to_uint64 x
    ``` *)
val uint128_to_uint64: a:t -> b:U64.t{U64.v b == v a % pow2 64}

(* To input / output constants *)
(* TODO: assume these without implementations *)
//val to_string: t -> Tot string
//val of_string: string -> Tot t

(* Multiplication primitives *)
(* Note that unlike UIntN, we do not provide uint128 * uint128 primitives (mul,
  mul_underspec, mul_mod, and mul_div) *)
(*| Widening product of a 64-bit and a 32-bit unsigned integer:
    `v (mul32 x y) == FStar.UInt64.v x * FStar.UInt32.v y`.

    No precondition; the product always fits in 128 bits. *)
val mul32: x:U64.t -> y:U32.t -> Pure t
  (requires True)
  (ensures (fun r -> v r == U64.v x * U32.v y))

(*| Widening product of two 64-bit unsigned integers:
    `v (mul_wide x y) == FStar.UInt64.v x * FStar.UInt64.v y`.

    No precondition; the product always fits in 128 bits.

    ```fstar
    let wide_product (x y: FStar.UInt64.t)
      : r:FStar.UInt128.t{FStar.UInt128.v r == FStar.UInt64.v x * FStar.UInt64.v y}
      = FStar.UInt128.mul_wide x y
    ``` *)
val mul_wide: x:U64.t -> y:U64.t -> Pure t
  (requires True)
  (ensures (fun r -> v r == U64.v x * U64.v y))

(* Infix notations. Deliberately the last declarations in this interface: a
   declaration of the interface is hidden from the implementation until the
   implementation has discharged everything that precedes it, so keeping these
   at the end means FStar.UInt128.fst never resolves [+] or [-] to this
   module's operators and always gets Prims' integer arithmetic. *)
(*| Infix notation for `FStar.UInt128.add`; requires the sum to fit. *)
inline_for_extraction noextract let ( + ) = add
(*| Infix notation for `FStar.UInt128.add_underspec`. *)
inline_for_extraction noextract let ( +?^ ) = add_underspec
(*| Infix notation for `FStar.UInt128.add_mod` (wrapping addition). *)
inline_for_extraction noextract let ( +%^ ) = add_mod
(*| Infix notation for `FStar.UInt128.sub`; requires `v b <= v a`. *)
inline_for_extraction noextract let ( - ) = sub
(*| Infix notation for `FStar.UInt128.sub_underspec`. *)
inline_for_extraction noextract let ( -?^ ) = sub_underspec
(*| Infix notation for `FStar.UInt128.sub_mod` (wrapping subtraction). *)
inline_for_extraction noextract let ( -%^ ) = sub_mod
(*| Infix notation for `FStar.UInt128.logand`. *)
inline_for_extraction noextract let ( &^ ) = logand
(*| Infix notation for `FStar.UInt128.logxor`. *)
inline_for_extraction noextract let ( ^^ ) = logxor
(*| Infix notation for `FStar.UInt128.logor`. *)
inline_for_extraction noextract let ( |^ ) = logor
(*| Infix notation for `FStar.UInt128.shift_left`. *)
inline_for_extraction noextract let ( <<^ ) = shift_left
(*| Infix notation for `FStar.UInt128.shift_right`. *)
inline_for_extraction noextract let ( >>^ ) = shift_right
(*| Infix notation for `FStar.UInt128.eq`. *)
inline_for_extraction noextract let ( =^ ) = eq
(*| Infix notation for `FStar.UInt128.gt`. *)
inline_for_extraction noextract let ( > ) = gt
(*| Infix notation for `FStar.UInt128.lt`. *)
inline_for_extraction noextract let ( < ) = lt
(*| Infix notation for `FStar.UInt128.gte`. *)
inline_for_extraction noextract let ( >= ) = gte
(*| Infix notation for `FStar.UInt128.lte`. *)
inline_for_extraction noextract let ( <= ) = lte

(* Deprecated infix notations: the spellings the six operators above had before
   type-based overloading made the [^] suffix unnecessary. *)
(*| Deprecated spelling of `FStar.UInt128.op_Plus` (`FStar.UInt128.add`). *)
[@@deprecated "use ( + )"]  inline_for_extraction noextract let ( +^ )  = add
(*| Deprecated spelling of `FStar.UInt128.op_Minus` (`FStar.UInt128.sub`). *)
[@@deprecated "use ( - )"]  inline_for_extraction noextract let ( -^ )  = sub
(*| Deprecated spelling of `FStar.UInt128.op_Greater` (`FStar.UInt128.gt`). *)
[@@deprecated "use ( > )"]  inline_for_extraction noextract let ( >^ )  = gt
(*| Deprecated spelling of `FStar.UInt128.op_Less` (`FStar.UInt128.lt`). *)
[@@deprecated "use ( < )"]  inline_for_extraction noextract let ( <^ )  = lt
(*| Deprecated spelling of `FStar.UInt128.op_Greater_Equals`
    (`FStar.UInt128.gte`). *)
[@@deprecated "use ( >= )"] inline_for_extraction noextract let ( >=^ ) = gte
(*| Deprecated spelling of `FStar.UInt128.op_Less_Equals`
    (`FStar.UInt128.lte`). *)
[@@deprecated "use ( <= )"] inline_for_extraction noextract let ( <=^ ) = lte
