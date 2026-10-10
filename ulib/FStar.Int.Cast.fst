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
module FStar.Int.Cast

module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8  = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

(*| Local alias of `FStar.Int.op_At_Percent`, the two's complement wrap-around modulo `v @% p`, which reduces `v` into `[-p/2, p/2)`.

    Used to state the contracts of the conversions to signed types that may not preserve the value. *)
let ( @% ) = FStar.Int.op_At_Percent

/// Unsigned to unsigned

(*| Converts an 8-bit unsigned integer to a 64-bit unsigned integer, preserving its value (zero extension).

    Total. The contract is `FStar.UInt64.v b = FStar.UInt8.v a`. *)
val uint8_to_uint64: a:U8.t -> Tot (b:U64.t{U64.v b = U8.v a})
let uint8_to_uint64 a = U64.uint_to_t (U8.v a)

(*| Converts an 8-bit unsigned integer to a 32-bit unsigned integer, preserving its value (zero extension).

    Total. The contract is `FStar.UInt32.v b = FStar.UInt8.v a`. *)
val uint8_to_uint32: a:U8.t -> Tot (b:U32.t{U32.v b = U8.v a})
let uint8_to_uint32 x = U32.uint_to_t (U8.v x)

(*| Converts an 8-bit unsigned integer to a 16-bit unsigned integer, preserving its value (zero extension).

    Total. The contract is `FStar.UInt16.v b = FStar.UInt8.v a`. *)
val uint8_to_uint16: a:U8.t -> Tot (b:U16.t{U16.v b = U8.v a})
let uint8_to_uint16 x = U16.uint_to_t (U8.v x)

(*| Converts a 16-bit unsigned integer to a 64-bit unsigned integer, preserving its value (zero extension).

    Total. The contract is `FStar.UInt64.v b = FStar.UInt16.v a`. *)
val uint16_to_uint64: a:U16.t -> Tot (b:U64.t{U64.v b = U16.v a})
let uint16_to_uint64 x = U64.uint_to_t (U16.v x)

(*| Converts a 16-bit unsigned integer to a 32-bit unsigned integer, preserving its value (zero extension).

    Total. The contract is `FStar.UInt32.v b = FStar.UInt16.v a`. *)
val uint16_to_uint32: a:U16.t -> Tot (b:U32.t{U32.v b = U16.v a})
let uint16_to_uint32 x = U32.uint_to_t (U16.v x)

(*| Converts a 16-bit unsigned integer to an 8-bit unsigned integer by truncation, keeping the low 8 bits.

    Total. The contract is `FStar.UInt8.v b = FStar.UInt16.v a % pow2 8`: the value is reduced modulo `pow2 8`, and preserved when it is less than `pow2 8`. *)
val uint16_to_uint8 : a:U16.t -> Tot (b:U8.t{U8.v b = U16.v a % pow2 8})
let uint16_to_uint8 x = U8.uint_to_t (U16.v x % pow2 8)

(*| Converts a 32-bit unsigned integer to a 64-bit unsigned integer, preserving its value (zero extension).

    Total. The contract is `FStar.UInt64.v b = FStar.UInt32.v a`. *)
val uint32_to_uint64: a:U32.t -> Tot (b:U64.t{U64.v b = U32.v a})
let uint32_to_uint64 x = U64.uint_to_t (U32.v x)

(*| Converts a 32-bit unsigned integer to a 16-bit unsigned integer by truncation, keeping the low 16 bits.

    Total. The contract is `FStar.UInt16.v b = FStar.UInt32.v a % pow2 16`: the value is reduced modulo `pow2 16`, and preserved when it is less than `pow2 16`. *)
val uint32_to_uint16: a:U32.t -> Tot (b:U16.t{U16.v b = U32.v a % pow2 16})
let uint32_to_uint16 x = U16.uint_to_t (U32.v x % pow2 16)

(*| Converts a 32-bit unsigned integer to an 8-bit unsigned integer by truncation, keeping the low 8 bits.

    Total. The contract is `FStar.UInt8.v b = FStar.UInt32.v a % pow2 8`: the value is reduced modulo `pow2 8`, and preserved when it is less than `pow2 8`.

    ```fstar
    let truncate_to_byte (x:FStar.UInt32.t{FStar.UInt32.v x == 0x1234})
      : Lemma (FStar.UInt8.v (FStar.Int.Cast.uint32_to_uint8 x) == 0x34)
      = ()
    ``` *)
val uint32_to_uint8 : a:U32.t -> Tot (b:U8.t{U8.v b = U32.v a % pow2 8})
let uint32_to_uint8 x = U8.uint_to_t (U32.v x % pow2 8)

(*| Converts a 64-bit unsigned integer to a 32-bit unsigned integer by truncation, keeping the low 32 bits.

    Total. The contract is `FStar.UInt32.v b = FStar.UInt64.v a % pow2 32`: the value is reduced modulo `pow2 32`, and preserved when it is less than `pow2 32`. *)
val uint64_to_uint32: a:U64.t -> Tot (b:U32.t{U32.v b = U64.v a % pow2 32})
let uint64_to_uint32 x = U32.uint_to_t (U64.v x % pow2 32)

(*| Converts a 64-bit unsigned integer to a 16-bit unsigned integer by truncation, keeping the low 16 bits.

    Total. The contract is `FStar.UInt16.v b = FStar.UInt64.v a % pow2 16`: the value is reduced modulo `pow2 16`, and preserved when it is less than `pow2 16`. *)
val uint64_to_uint16: a:U64.t -> Tot (b:U16.t{U16.v b = U64.v a % pow2 16})
let uint64_to_uint16 x = U16.uint_to_t (U64.v x % pow2 16)

(*| Converts a 64-bit unsigned integer to an 8-bit unsigned integer by truncation, keeping the low 8 bits.

    Total. The contract is `FStar.UInt8.v b = FStar.UInt64.v a % pow2 8`: the value is reduced modulo `pow2 8`, and preserved when it is less than `pow2 8`. *)
val uint64_to_uint8 : a:U64.t -> Tot (b:U8.t{U8.v b = U64.v a % pow2 8})
let uint64_to_uint8 x = U8.uint_to_t (U64.v x % pow2 8)

/// Signed to signed

(*| Converts an 8-bit signed integer to a 64-bit signed integer, preserving its value (sign extension).

    Total. The contract is `FStar.Int64.v b = FStar.Int8.v a`. *)
val int8_to_int64: a:I8.t -> Tot (b:I64.t{I64.v b = I8.v a})
let int8_to_int64 x = I64.int_to_t (I8.v x)

(*| Converts an 8-bit signed integer to a 32-bit signed integer, preserving its value (sign extension).

    Total. The contract is `FStar.Int32.v b = FStar.Int8.v a`.

    ```fstar
    let sign_extend (x:FStar.Int8.t)
      : Lemma (FStar.Int32.v (FStar.Int.Cast.int8_to_int32 x) == FStar.Int8.v x)
      = ()
    ``` *)
val int8_to_int32: a:I8.t -> Tot (b:I32.t{I32.v b = I8.v a})
let int8_to_int32 x = I32.int_to_t (I8.v x)

(*| Converts an 8-bit signed integer to a 16-bit signed integer, preserving its value (sign extension).

    Total. The contract is `FStar.Int16.v b = FStar.Int8.v a`. *)
val int8_to_int16: a:I8.t -> Tot (b:I16.t{I16.v b = I8.v a})
let int8_to_int16 x = I16.int_to_t (I8.v x)

(*| Converts a 16-bit signed integer to a 64-bit signed integer, preserving its value (sign extension).

    Total. The contract is `FStar.Int64.v b = FStar.Int16.v a`. *)
val int16_to_int64: a:I16.t -> Tot (b:I64.t{I64.v b = I16.v a})
let int16_to_int64 x = I64.int_to_t (I16.v x @% pow2 64)

(*| Converts a 16-bit signed integer to a 32-bit signed integer, preserving its value (sign extension).

    Total. The contract is `FStar.Int32.v b = FStar.Int16.v a`. *)
val int16_to_int32: a:I16.t -> Tot (b:I32.t{I32.v b = I16.v a})
let int16_to_int32 x = I32.int_to_t (I16.v x @% pow2 32)

(*| Converts a 16-bit signed integer to an 8-bit signed integer with two's complement wrap-around, keeping the low 8 bits.

    Total. The contract is `FStar.Int8.v b = (FStar.Int16.v a @% pow2 8)`: the value is preserved when it fits in 8 signed bits, and otherwise wraps into `[-pow2 7, pow2 7)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val int16_to_int8 : a:I16.t -> Tot (b:I8.t {I8.v b  = (I16.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int16_to_int8 x = I8.int_to_t (I16.v x @% pow2 8)

(*| Converts a 32-bit signed integer to a 64-bit signed integer, preserving its value (sign extension).

    Total. The contract is `FStar.Int64.v b = FStar.Int32.v a`. *)
val int32_to_int64: a:I32.t -> Tot (b:I64.t{I64.v b = I32.v a})
let int32_to_int64 x = I64.int_to_t (I32.v x @% pow2 64)

(*| Converts a 32-bit signed integer to a 16-bit signed integer with two's complement wrap-around, keeping the low 16 bits.

    Total. The contract is `FStar.Int16.v b = (FStar.Int32.v a @% pow2 16)`: the value is preserved when it fits in 16 signed bits, and otherwise wraps into `[-pow2 15, pow2 15)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val int32_to_int16: a:I32.t -> Tot (b:I16.t{I16.v b = (I32.v a @% pow2 16)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int32_to_int16 x = I16.int_to_t (I32.v x @% pow2 16)

(*| Converts a 32-bit signed integer to an 8-bit signed integer with two's complement wrap-around, keeping the low 8 bits.

    Total. The contract is `FStar.Int8.v b = (FStar.Int32.v a @% pow2 8)`: the value is preserved when it fits in 8 signed bits, and otherwise wraps into `[-pow2 7, pow2 7)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val int32_to_int8 : a:I32.t -> Tot (b:I8.t {I8.v b  = (I32.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int32_to_int8 x = I8.int_to_t (I32.v x @% pow2 8)

(*| Converts a 64-bit signed integer to a 32-bit signed integer with two's complement wrap-around, keeping the low 32 bits.

    Total. The contract is `FStar.Int32.v b = (FStar.Int64.v a @% pow2 32)`: the value is preserved when it fits in 32 signed bits, and otherwise wraps into `[-pow2 31, pow2 31)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val int64_to_int32: a:I64.t -> Tot (b:I32.t{I32.v b = (I64.v a @% pow2 32)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int64_to_int32 x = I32.int_to_t (I64.v x @% pow2 32)

(*| Converts a 64-bit signed integer to a 16-bit signed integer with two's complement wrap-around, keeping the low 16 bits.

    Total. The contract is `FStar.Int16.v b = (FStar.Int64.v a @% pow2 16)`: the value is preserved when it fits in 16 signed bits, and otherwise wraps into `[-pow2 15, pow2 15)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val int64_to_int16: a:I64.t -> Tot (b:I16.t{I16.v b = (I64.v a @% pow2 16)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int64_to_int16 x = I16.int_to_t (I64.v x @% pow2 16)

(*| Converts a 64-bit signed integer to an 8-bit signed integer with two's complement wrap-around, keeping the low 8 bits.

    Total. The contract is `FStar.Int8.v b = (FStar.Int64.v a @% pow2 8)`: the value is preserved when it fits in 8 signed bits, and otherwise wraps into `[-pow2 7, pow2 7)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val int64_to_int8 : a:I64.t -> Tot (b:I8.t {I8.v b  = (I64.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int64_to_int8 x = I8.int_to_t (I64.v x @% pow2 8)

/// Unsigned to signed

(*| Converts an 8-bit unsigned integer to a 64-bit signed integer, preserving its value (zero extension).

    Total. The contract is `FStar.Int64.v b = FStar.UInt8.v a`. *)
val uint8_to_int64: a:U8.t -> Tot (b:I64.t{I64.v b = U8.v a})
let uint8_to_int64 x = I64.int_to_t (U8.v x)

(*| Converts an 8-bit unsigned integer to a 32-bit signed integer, preserving its value (zero extension).

    Total. The contract is `FStar.Int32.v b = FStar.UInt8.v a`. *)
val uint8_to_int32: a:U8.t -> Tot (b:I32.t{I32.v b = U8.v a})
let uint8_to_int32 x = I32.int_to_t (U8.v x)

(*| Converts an 8-bit unsigned integer to a 16-bit signed integer, preserving its value (zero extension).

    Total. The contract is `FStar.Int16.v b = FStar.UInt8.v a`. *)
val uint8_to_int16: a:U8.t -> Tot (b:I16.t{I16.v b = U8.v a})
let uint8_to_int16 x = I16.int_to_t (U8.v x)

(*| Converts an 8-bit unsigned integer to an 8-bit signed integer with two's complement wrap-around, keeping the low 8 bits.

    Total. The contract is `FStar.Int8.v b = (FStar.UInt8.v a @% pow2 8)`: the value is preserved when it fits in 8 signed bits, and otherwise wraps into `[-pow2 7, pow2 7)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint8_to_int8 : a:U8.t -> Tot (b:I8.t {I8.v b  = (U8.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint8_to_int8 x = I8.int_to_t (U8.v x @% pow2 8)

(*| Converts a 16-bit unsigned integer to a 64-bit signed integer, preserving its value (zero extension).

    Total. The contract is `FStar.Int64.v b = FStar.UInt16.v a`. *)
val uint16_to_int64: a:U16.t -> Tot (b:I64.t{I64.v b = U16.v a})
let uint16_to_int64 x = I64.int_to_t (U16.v x)

(*| Converts a 16-bit unsigned integer to a 32-bit signed integer, preserving its value (zero extension).

    Total. The contract is `FStar.Int32.v b = FStar.UInt16.v a`. *)
val uint16_to_int32: a:U16.t -> Tot (b:I32.t{I32.v b = U16.v a})
let uint16_to_int32 x = I32.int_to_t (U16.v x)

(*| Converts a 16-bit unsigned integer to a 16-bit signed integer with two's complement wrap-around, keeping the low 16 bits.

    Total. The contract is `FStar.Int16.v b = (FStar.UInt16.v a @% pow2 16)`: the value is preserved when it fits in 16 signed bits, and otherwise wraps into `[-pow2 15, pow2 15)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint16_to_int16: a:U16.t -> Tot (b:I16.t{I16.v b = (U16.v a @% pow2 16)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint16_to_int16 x = I16.int_to_t (U16.v x @% pow2 16)

(*| Converts a 16-bit unsigned integer to an 8-bit signed integer with two's complement wrap-around, keeping the low 8 bits.

    Total. The contract is `FStar.Int8.v b = (FStar.UInt16.v a @% pow2 8)`: the value is preserved when it fits in 8 signed bits, and otherwise wraps into `[-pow2 7, pow2 7)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint16_to_int8 : a:U16.t -> Tot (b:I8.t {I8.v b  = (U16.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint16_to_int8 x = I8.int_to_t (U16.v x @% pow2 8)

(*| Converts a 32-bit unsigned integer to a 64-bit signed integer, preserving its value (zero extension).

    Total. The contract is `FStar.Int64.v b = FStar.UInt32.v a`. *)
val uint32_to_int64: a:U32.t -> Tot (b:I64.t{I64.v b = U32.v a})
let uint32_to_int64 x = I64.int_to_t (U32.v x)

(*| Converts a 32-bit unsigned integer to a 32-bit signed integer with two's complement wrap-around, keeping the low 32 bits.

    Total. The contract is `FStar.Int32.v b = (FStar.UInt32.v a @% pow2 32)`: the value is preserved when it fits in 32 signed bits, and otherwise wraps into `[-pow2 31, pow2 31)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint32_to_int32: a:U32.t -> Tot (b:I32.t{I32.v b = (U32.v a @% pow2 32)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint32_to_int32 x = I32.int_to_t (U32.v x @% pow2 32)

(*| Converts a 32-bit unsigned integer to a 16-bit signed integer with two's complement wrap-around, keeping the low 16 bits.

    Total. The contract is `FStar.Int16.v b = (FStar.UInt32.v a @% pow2 16)`: the value is preserved when it fits in 16 signed bits, and otherwise wraps into `[-pow2 15, pow2 15)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint32_to_int16: a:U32.t -> Tot (b:I16.t{I16.v b = (U32.v a @% pow2 16)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint32_to_int16 x = I16.int_to_t (U32.v x @% pow2 16)

(*| Converts a 32-bit unsigned integer to an 8-bit signed integer with two's complement wrap-around, keeping the low 8 bits.

    Total. The contract is `FStar.Int8.v b = (FStar.UInt32.v a @% pow2 8)`: the value is preserved when it fits in 8 signed bits, and otherwise wraps into `[-pow2 7, pow2 7)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint32_to_int8 : a:U32.t -> Tot (b:I8.t {I8.v b  = (U32.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint32_to_int8 x = I8.int_to_t (U32.v x @% pow2 8)

(*| Converts a 64-bit unsigned integer to a 64-bit signed integer with two's complement wrap-around, keeping the low 64 bits.

    Total. The contract is `FStar.Int64.v b = (FStar.UInt64.v a @% pow2 64)`: the value is preserved when it fits in 64 signed bits, and otherwise wraps into `[-pow2 63, pow2 63)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint64_to_int64: a:U64.t -> Tot (b:I64.t{I64.v b = (U64.v a @% pow2 64)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint64_to_int64 x = I64.int_to_t (U64.v x @% pow2 64)

(*| Converts a 64-bit unsigned integer to a 32-bit signed integer with two's complement wrap-around, keeping the low 32 bits.

    Total. The contract is `FStar.Int32.v b = (FStar.UInt64.v a @% pow2 32)`: the value is preserved when it fits in 32 signed bits, and otherwise wraps into `[-pow2 31, pow2 31)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint64_to_int32: a:U64.t -> Tot (b:I32.t{I32.v b = (U64.v a @% pow2 32)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint64_to_int32 x = I32.int_to_t (U64.v x @% pow2 32)

(*| Converts a 64-bit unsigned integer to a 16-bit signed integer with two's complement wrap-around, keeping the low 16 bits.

    Total. The contract is `FStar.Int16.v b = (FStar.UInt64.v a @% pow2 16)`: the value is preserved when it fits in 16 signed bits, and otherwise wraps into `[-pow2 15, pow2 15)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint64_to_int16: a:U64.t -> Tot (b:I16.t{I16.v b = (U64.v a @% pow2 16)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint64_to_int16 x = I16.int_to_t (U64.v x @% pow2 16)

(*| Converts a 64-bit unsigned integer to an 8-bit signed integer with two's complement wrap-around, keeping the low 8 bits.

    Total. The contract is `FStar.Int8.v b = (FStar.UInt64.v a @% pow2 8)`: the value is preserved when it fits in 8 signed bits, and otherwise wraps into `[-pow2 7, pow2 7)`.

    Marked deprecated ("with care"): in C the result of this conversion is implementation-defined when the value is not representable, so check that the value fits or that the wrapping is intended. *)
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint64_to_int8 : a:U64.t -> Tot (b:I8.t {I8.v b  = (U64.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint64_to_int8 x = I8.int_to_t (U64.v x @% pow2 8)

/// Signed to unsigned

(*| Converts an 8-bit signed integer to a 64-bit unsigned integer modulo `pow2 64` (sign extension followed by reinterpretation as unsigned).

    Total. The contract is `FStar.UInt64.v b = FStar.Int8.v a % pow2 64`, with the Euclidean `%`: nonnegative values are preserved and a negative value `x` becomes `x + pow2 64`. *)
val int8_to_uint64: a:I8.t -> Tot (b:U64.t{U64.v b = I8.v a % pow2 64})
let int8_to_uint64 x = U64.uint_to_t (I8.v x % pow2 64)

(*| Converts an 8-bit signed integer to a 32-bit unsigned integer modulo `pow2 32` (sign extension followed by reinterpretation as unsigned).

    Total. The contract is `FStar.UInt32.v b = FStar.Int8.v a % pow2 32`, with the Euclidean `%`: nonnegative values are preserved and a negative value `x` becomes `x + pow2 32`. *)
val int8_to_uint32: a:I8.t -> Tot (b:U32.t{U32.v b = I8.v a % pow2 32})
let int8_to_uint32 x = U32.uint_to_t (I8.v x % pow2 32)

(*| Converts an 8-bit signed integer to a 16-bit unsigned integer modulo `pow2 16` (sign extension followed by reinterpretation as unsigned).

    Total. The contract is `FStar.UInt16.v b = FStar.Int8.v a % pow2 16`, with the Euclidean `%`: nonnegative values are preserved and a negative value `x` becomes `x + pow2 16`. *)
val int8_to_uint16: a:I8.t -> Tot (b:U16.t{U16.v b = I8.v a % pow2 16})
let int8_to_uint16 x = U16.uint_to_t (I8.v x % pow2 16)

(*| Converts an 8-bit signed integer to an 8-bit unsigned integer modulo `pow2 8` (reinterpretation of the same two's complement bits as unsigned).

    Total. The contract is `FStar.UInt8.v b = FStar.Int8.v a % pow2 8`, with the Euclidean `%`: nonnegative values are preserved and a negative value `x` becomes `x + pow2 8`. *)
val int8_to_uint8 : a:I8.t -> Tot (b:U8.t {U8.v b  = I8.v a % pow2 8})
let int8_to_uint8 x = U8.uint_to_t (I8.v x % pow2 8)

(*| Converts a 16-bit signed integer to a 64-bit unsigned integer modulo `pow2 64` (sign extension followed by reinterpretation as unsigned).

    Total. The contract is `FStar.UInt64.v b = FStar.Int16.v a % pow2 64`, with the Euclidean `%`: nonnegative values are preserved and a negative value `x` becomes `x + pow2 64`. *)
val int16_to_uint64: a:I16.t -> Tot (b:U64.t{U64.v b = I16.v a % pow2 64})
let int16_to_uint64 x = U64.uint_to_t (I16.v x % pow2 64)

(*| Converts a 16-bit signed integer to a 32-bit unsigned integer modulo `pow2 32` (sign extension followed by reinterpretation as unsigned).

    Total. The contract is `FStar.UInt32.v b = FStar.Int16.v a % pow2 32`, with the Euclidean `%`: nonnegative values are preserved and a negative value `x` becomes `x + pow2 32`. *)
val int16_to_uint32: a:I16.t -> Tot (b:U32.t{U32.v b = I16.v a % pow2 32})
let int16_to_uint32 x = U32.uint_to_t (I16.v x % pow2 32)

(*| Converts a 16-bit signed integer to a 16-bit unsigned integer modulo `pow2 16` (reinterpretation of the same two's complement bits as unsigned).

    Total. The contract is `FStar.UInt16.v b = FStar.Int16.v a % pow2 16`, with the Euclidean `%`: nonnegative values are preserved and a negative value `x` becomes `x + pow2 16`. *)
val int16_to_uint16: a:I16.t -> Tot (b:U16.t{U16.v b = I16.v a % pow2 16})
let int16_to_uint16 x = U16.uint_to_t (I16.v x % pow2 16)

(*| Converts a 16-bit signed integer to an 8-bit unsigned integer modulo `pow2 8` (truncation to the low 8 bits of the two's complement representation).

    Total. The contract is `FStar.UInt8.v b = FStar.Int16.v a % pow2 8`, with the Euclidean `%`: values in `[0, pow2 8)` are preserved, and in general the result is the low 8 bits of the two's complement representation read as unsigned. *)
val int16_to_uint8 : a:I16.t -> Tot (b:U8.t {U8.v b  = I16.v a % pow2 8})
let int16_to_uint8 x = U8.uint_to_t (I16.v x % pow2 8)

(*| Converts a 32-bit signed integer to a 64-bit unsigned integer modulo `pow2 64` (sign extension followed by reinterpretation as unsigned).

    Total. The contract is `FStar.UInt64.v b = FStar.Int32.v a % pow2 64`, with the Euclidean `%`: nonnegative values are preserved and a negative value `x` becomes `x + pow2 64`. *)
val int32_to_uint64: a:I32.t -> Tot (b:U64.t{U64.v b = I32.v a % pow2 64})
let int32_to_uint64 x = U64.uint_to_t (I32.v x % pow2 64)

(*| Converts a 32-bit signed integer to a 32-bit unsigned integer modulo `pow2 32` (reinterpretation of the same two's complement bits as unsigned).

    Total. The contract is `FStar.UInt32.v b = FStar.Int32.v a % pow2 32`, with the Euclidean `%`: nonnegative values are preserved and a negative value `x` becomes `x + pow2 32`. *)
val int32_to_uint32: a:I32.t -> Tot (b:U32.t{U32.v b = I32.v a % pow2 32})
let int32_to_uint32 x = U32.uint_to_t (I32.v x % pow2 32)

(*| Converts a 32-bit signed integer to a 16-bit unsigned integer modulo `pow2 16` (truncation to the low 16 bits of the two's complement representation).

    Total. The contract is `FStar.UInt16.v b = FStar.Int32.v a % pow2 16`, with the Euclidean `%`: values in `[0, pow2 16)` are preserved, and in general the result is the low 16 bits of the two's complement representation read as unsigned. *)
val int32_to_uint16: a:I32.t -> Tot (b:U16.t{U16.v b = I32.v a % pow2 16})
let int32_to_uint16 x = U16.uint_to_t (I32.v x % pow2 16)

(*| Converts a 32-bit signed integer to an 8-bit unsigned integer modulo `pow2 8` (truncation to the low 8 bits of the two's complement representation).

    Total. The contract is `FStar.UInt8.v b = FStar.Int32.v a % pow2 8`, with the Euclidean `%`: values in `[0, pow2 8)` are preserved, and in general the result is the low 8 bits of the two's complement representation read as unsigned.

    ```fstar
    let minus_one_as_byte (x:FStar.Int32.t{FStar.Int32.v x == -1})
      : Lemma (FStar.UInt8.v (FStar.Int.Cast.int32_to_uint8 x) == 255)
      = ()
    ``` *)
val int32_to_uint8 : a:I32.t -> Tot (b:U8.t {U8.v b  = I32.v a % pow2 8})
let int32_to_uint8 x = U8.uint_to_t (I32.v x % pow2 8)

(*| Converts a 64-bit signed integer to a 64-bit unsigned integer modulo `pow2 64` (reinterpretation of the same two's complement bits as unsigned).

    Total. The contract is `FStar.UInt64.v b = FStar.Int64.v a % pow2 64`, with the Euclidean `%`: nonnegative values are preserved and a negative value `x` becomes `x + pow2 64`. *)
val int64_to_uint64: a:I64.t -> Tot (b:U64.t{U64.v b = I64.v a % pow2 64})
let int64_to_uint64 x = U64.uint_to_t (I64.v x % pow2 64)

(*| Converts a 64-bit signed integer to a 32-bit unsigned integer modulo `pow2 32` (truncation to the low 32 bits of the two's complement representation).

    Total. The contract is `FStar.UInt32.v b = FStar.Int64.v a % pow2 32`, with the Euclidean `%`: values in `[0, pow2 32)` are preserved, and in general the result is the low 32 bits of the two's complement representation read as unsigned. *)
val int64_to_uint32: a:I64.t -> Tot (b:U32.t{U32.v b = I64.v a % pow2 32})
let int64_to_uint32 x = U32.uint_to_t (I64.v x % pow2 32)

(*| Converts a 64-bit signed integer to a 16-bit unsigned integer modulo `pow2 16` (truncation to the low 16 bits of the two's complement representation).

    Total. The contract is `FStar.UInt16.v b = FStar.Int64.v a % pow2 16`, with the Euclidean `%`: values in `[0, pow2 16)` are preserved, and in general the result is the low 16 bits of the two's complement representation read as unsigned. *)
val int64_to_uint16: a:I64.t -> Tot (b:U16.t{U16.v b = I64.v a % pow2 16})
let int64_to_uint16 x = U16.uint_to_t (I64.v x % pow2 16)

(*| Converts a 64-bit signed integer to an 8-bit unsigned integer modulo `pow2 8` (truncation to the low 8 bits of the two's complement representation).

    Total. The contract is `FStar.UInt8.v b = FStar.Int64.v a % pow2 8`, with the Euclidean `%`: values in `[0, pow2 8)` are preserved, and in general the result is the low 8 bits of the two's complement representation read as unsigned. *)
val int64_to_uint8 : a:I64.t -> Tot (b:U8.t {U8.v b  = I64.v a % pow2 8})
let int64_to_uint8 x = U8.uint_to_t (I64.v x % pow2 8)
