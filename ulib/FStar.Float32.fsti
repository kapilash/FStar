module FStar.Float32

(*| Abstract primitive type of 32-bit floating-point numbers.

    The type and every operation of `FStar.Float32` are assumed: the interface states no arithmetic properties (no rounding, ordering or IEEE 754 laws) that proofs can use. The interface provides no `hasEq` instance; compare values with `FStar.Float32.ieee_eq` or `FStar.Float32.bit_eq`. *)
new
val t : Type0

(*| Alias of `FStar.Float32.t`, marked `inline_for_extraction`. *)
inline_for_extraction
let float32 = t

(*| Converts a 64-bit signed integer to a 32-bit float.

    Assumed; the interface does not specify the result, in particular for integers that are not exactly representable. *)
val of_int : Int64.t -> t

(*| The float obtained from the integer 0 by `FStar.Float32.of_int`. *)
inline_for_extraction
let zero = of_int 0L
(*| The float obtained from the integer 1 by `FStar.Float32.of_int`. *)
inline_for_extraction
let one  = of_int 1L

(*| Floating-point addition. Assumed; the interface does not specify the result. *)
val add : t -> t -> t
(*| Floating-point subtraction. Assumed; the interface does not specify the result. *)
val sub : t -> t -> t
(*| Floating-point multiplication. Assumed; the interface does not specify the result. *)
val mul : t -> t -> t
(*| Floating-point division. Assumed; the interface does not specify the result, including division by zero. *)
val div : t -> t -> t

(*| Floating-point comparison, intended as `x < y`. Assumed; the interface does not specify the result. *)
val lt  : t -> t -> bool
(*| Floating-point comparison, intended as `x <= y`. Assumed; the interface does not specify the result. *)
val lte : t -> t -> bool

(*| IEEE 754 equality of floats: identifies `+0.0` and `-0.0`, and returns `false` when either argument is a NaN.

    This is not bit equality; see `FStar.Float32.bit_eq`. The behaviour is described informally and assumed: no lemma states it. *)
val ieee_eq  : t -> t -> bool

(*| Bit-level equality of floats: distinguishes `+0.0` and `-0.0` and, unlike `FStar.Float32.ieee_eq`, a NaN is equal to itself.

    The behaviour is described informally and assumed: no lemma states it. *)
val bit_eq  : t -> t -> bool

(*| The float denoted by a literal string such as `"3.14"`.

    It must be called with a concrete string literal: during extraction to C it is replaced by the corresponding C floating-point constant. Assumed; the interface does not specify the result or the accepted syntax. *)
val of_literal : string -> t

(*| A string representation of a float, for debugging and tests.

    Assumed; the interface does not specify the format. *)
val to_string : t -> string
