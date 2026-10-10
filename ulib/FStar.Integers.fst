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
module FStar.Integers

#set-options "--ifuel 2 --fuel 0"

(*| Attribute marking the definitions of this module that
    `FStar.Integers.norm` unfolds.

    Its value is irrelevant; it is used as `[@@mark_for_norm]`. *)
irreducible
let mark_for_norm = ()

(*| Normalizes `x` by unfolding the definitions marked with
    `FStar.Integers.mark_for_norm` and reducing matches (`iota`).

    Used in the refinements of this module so that, once a concrete
    `FStar.Integers.signed_width` is known, bounds and conversions reduce to
    those of the underlying machine-integer module. *)
unfold
let norm (#a:Type) (x:a) = norm [iota; delta_attr [`%mark_for_norm]] x

(*| The bit widths supported by the overloaded integer operations:
    `W8`, `W16`, `W32`, `W64`, `W128`, and `Winfinite` for unbounded
    mathematical integers.

    See `FStar.Integers.nat_of_width` for the number of bits of each. *)
type width =
  | W8
  | W16
  | W32
  | W64
  | W128
  | Winfinite

(*| The number of bits of a width: `Some 8` to `Some 128` for the fixed
    widths, and `None` for `Winfinite`. *)
[@@mark_for_norm]
let nat_of_width = function
  | W8   -> Some 8
  | W16  -> Some 16
  | W32  -> Some 32
  | W64  -> Some 64
  | W128 -> Some 128
  | Winfinite -> None

(*| The widths other than `Winfinite`. *)
let fixed_width = w:width{w <> Winfinite}

(*| The number of bits of a fixed width, from 8 to 128. *)
[@@mark_for_norm]
let nat_of_fixed_width (w:fixed_width) =
  match nat_of_width w with
  | Some v -> v

(*| A signedness together with a width, indexing the integer types of
    `FStar.Integers.int_t`.

    `Signed w` is the signed type of width `w`, where `Signed Winfinite`
    denotes the mathematical integers. `Unsigned w` is the unsigned type of a
    fixed width `w`; there is no unbounded unsigned type, use
    `FStar.Integers.nat` instead. *)
type signed_width =
  | Signed of width
  | Unsigned of fixed_width //We don't support (Unsigned WInfinite); use nat instead

(*| The width component of a `FStar.Integers.signed_width`. *)
[@@mark_for_norm]
let width_of_sw = function
  | Signed w -> w
  | Unsigned w -> w

(*| The integer type selected by a `FStar.Integers.signed_width`.

    `Unsigned W8` to `Unsigned W128` map to `FStar.UInt8.t` to
    `FStar.UInt128.t`, `Signed W8` to `Signed W128` map to `FStar.Int8.t` to
    `FStar.Int128.t`, and `Signed Winfinite` maps to `Prims.int`. The
    operators of this module are overloaded over this index. *)
[@@mark_for_norm]
noextract
inline_for_extraction
let int_t sw : Tot Type0 =
  match sw with
  | Unsigned W8 -> FStar.UInt8.t
  | Unsigned W16 -> FStar.UInt16.t
  | Unsigned W32 -> FStar.UInt32.t
  | Unsigned W64 -> FStar.UInt64.t
  | Unsigned W128 -> FStar.UInt128.t
  | Signed Winfinite -> int
  | Signed W8 -> FStar.Int8.t
  | Signed W16 -> FStar.Int16.t
  | Signed W32 -> FStar.Int32.t
  | Signed W64 -> FStar.Int64.t
  | Signed W128 -> FStar.Int128.t

(*| The unnormalized form of `FStar.Integers.within_bounds`.

    It is `FStar.UInt.size x n` for unsigned `n`-bit widths,
    `FStar.Int.size x n` for signed `n`-bit widths, and `True` for
    `Signed Winfinite`. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let within_bounds' sw (x:int) =
  match sw, nat_of_width (width_of_sw sw) with
  | Signed _,   None   -> True
  | Signed _,   Some n -> FStar.Int.size x n
  | Unsigned _, Some n -> FStar.UInt.size x n

(*| Holds when the integer `x` is representable in the type
    `FStar.Integers.int_t sw`.

    The normalized form of `FStar.Integers.within_bounds'`: for a concrete
    `sw` it reduces to the range condition of that type, and to `True` for
    `Signed Winfinite`. It is the precondition of the non-wrapping
    operations of this module. *)
unfold
let within_bounds sw x = norm (within_bounds' sw x)

(*| The mathematical value of an integer of any width, as a `Prims.int`
    within the bounds of its type.

    Dispatches to the `v` function of the underlying module, for example
    `FStar.UInt32.v`; it is the identity on `Signed Winfinite`. Marked
    `noextract`. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let v #sw (x:int_t sw)
  : Tot (y:int_t (Signed Winfinite){within_bounds sw y})
  = match sw with
    | Unsigned w ->
      (match w with
       | W8 -> FStar.UInt8.v x
       | W16 -> FStar.UInt16.v x
       | W32 -> FStar.UInt32.v x
       | W64 -> FStar.UInt64.v x
       | W128 -> FStar.UInt128.v x)
    | Signed w ->
      (match w with
       | Winfinite -> x
       | W8 -> FStar.Int8.v x
       | W16 -> FStar.Int16.v x
       | W32 -> FStar.Int32.v x
       | W64 -> FStar.Int64.v x
       | W128 -> FStar.Int128.v x)

(*| Converts a mathematical integer to the integer type indexed by `sw`,
    preserving its value.

    Requires `FStar.Integers.within_bounds sw x`; dispatches to the
    `uint_to_t` or `int_to_t` function of the underlying module. The inverse
    of `FStar.Integers.v`. Marked `noextract`. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let u    #sw
        (x:int_t (Signed Winfinite){within_bounds sw x})
  : Tot (y:int_t sw{norm (v x == v y)})
  = match sw with
    | Unsigned w ->
      (match w with
       | W8 -> FStar.UInt8.uint_to_t x
       | W16 -> FStar.UInt16.uint_to_t x
       | W32 -> FStar.UInt32.uint_to_t x
       | W64 -> FStar.UInt64.uint_to_t x
       | W128 -> FStar.UInt128.uint_to_t x)
    | Signed w ->
      (match w with
       | Winfinite -> x
       | W8 -> FStar.Int8.int_to_t x
       | W16 -> FStar.Int16.int_to_t x
       | W32 -> FStar.Int32.int_to_t x
       | W64 -> FStar.Int64.int_to_t x
       | W128 -> FStar.Int128.int_to_t x)

(*| Converts an integer between any two widths and signednesses, preserving
    its value.

    Requires the value to be within the bounds of the target type
    (`FStar.Integers.cast_ok`); it never truncates or wraps. Defined as
    `u (v from)`, and marked `irreducible` and `noextract`.

    ```fstar
    let widen_u8 (x: uint_8) : uint_32 = cast x
    ``` *)
irreducible
noextract
let cast #sw #sw'
         (from:int_t sw{within_bounds sw' (v from)})
   : Tot (to:int_t sw'{norm (v from == v to)})
   = u (v from)

(*| Holds when `FStar.Integers.cast` can convert `x` to the type indexed by
    `to`, that is when the value of `x` is within the bounds of that type. *)
[@@mark_for_norm]
unfold
noextract
let cast_ok #from to (x:int_t from) = within_bounds to (v x)

(*| Overloaded addition without overflow, at any width.

    Requires the sum to be within bounds
    (`FStar.Integers.within_bounds sw (v x + v y)`). For a concrete width it
    unfolds to the addition of the underlying module, for example
    `FStar.UInt32.add`, whose contract gives `v (x + y) == v x + v y`; on
    `Signed Winfinite` it is `Prims.op_Addition`.

    ```fstar
    let add_u32 (x: uint_32) (y: uint_32{ok (+) x y}) : uint_32 = x + y
    ``` *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( + ) #sw
          (x:int_t sw)
          (y:int_t sw{within_bounds sw (v x + v y)})
  : Tot   (int_t sw)
  = match sw with
    | Signed Winfinite -> x + y
    | Unsigned W8   -> FStar.UInt8.(x + y)
    | Unsigned W16  -> FStar.UInt16.(x + y)
    | Unsigned W32  -> FStar.UInt32.(x + y)
    | Unsigned W64  -> FStar.UInt64.(x + y)
    | Unsigned W128 -> FStar.UInt128.(x + y)
    | Signed W8   -> FStar.Int8.(x + y)
    | Signed W16  -> FStar.Int16.(x + y)
    | Signed W32  -> FStar.Int32.(x + y)
    | Signed W64  -> FStar.Int64.(x + y)
    | Signed W128 -> FStar.Int128.(x + y)

(*| Overloaded unsigned addition with no precondition whose result is only
    specified when the sum does not overflow.

    Only for unsigned fixed widths; unfolds to the `add_underspec` of the
    underlying module, for example `FStar.UInt32.add_underspec`. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( +? ) (#w:fixed_width)
           (x:int_t (Unsigned w))
           (y:int_t (Unsigned w))
  : Tot    (int_t (Unsigned w))
  = match w with
    | W8 -> FStar.UInt8.(x +?^ y)
    | W16 -> FStar.UInt16.(x +?^ y)
    | W32 -> FStar.UInt32.(x +?^ y)
    | W64 -> FStar.UInt64.(x +?^ y)
    | W128 -> FStar.UInt128.(x +?^ y)

(*| Reduces `x` modulo `y` according to the signedness of `sw`.

    For unsigned widths it is `x % y`; for signed widths it is
    `FStar.Int.op_At_Percent`, the two's complement wrap-around into
    `[-y/2, y/2)`, which requires `y` to be even. Total; marked `noextract`. *)
[@@mark_for_norm; strict_on_arguments [0]]
noextract
let modulo sw (x:int) (y:pos{Signed? sw ==> y%2=0}) =
  match sw with
  | Unsigned _ ->  x % y
  | _ -> FStar.Int.(x @% y)

(*| Overloaded wrapping addition for unsigned fixed widths:
    `v (x +% y) == (v x + v y) % pow2 n` for width `n`.

    No precondition. Unfolds to the `add_mod` of the underlying module, for
    example `FStar.UInt8.add_mod`. Not available for signed types.

    ```fstar
    let wrap_u8 (x y: uint_8) : uint_8 = x +% y
    ``` *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( +% ) (#sw:_{Unsigned? sw})
           (x:int_t sw)
           (y:int_t sw)
  : Tot    (int_t sw)
  = let Unsigned w = sw in
    match w with
    | W8 -> FStar.UInt8.(x +%^ y)
    | W16 -> FStar.UInt16.(x +%^ y)
    | W32 -> FStar.UInt32.(x +%^ y)
    | W64 -> FStar.UInt64.(x +%^ y)
    | W128 -> FStar.UInt128.(x +%^ y)

(*| Overloaded subtraction without overflow, at any width.

    Requires the difference to be within bounds
    (`FStar.Integers.within_bounds sw (v x - v y)`). For a concrete width it
    unfolds to the subtraction of the underlying module, whose contract gives
    `v (x - y) == v x - v y`. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( - ) #sw
                   (x:int_t sw)
                   (y:int_t sw{within_bounds sw (v x - v y)})
    : Tot          (int_t sw)
  = match sw with
    | Signed Winfinite -> x - y
    | Unsigned W8 -> FStar.UInt8.(x - y)
    | Unsigned W16 -> FStar.UInt16.(x - y)
    | Unsigned W32 -> FStar.UInt32.(x - y)
    | Unsigned W64 -> FStar.UInt64.(x - y)
    | Unsigned W128 -> FStar.UInt128.(x - y)
    | Signed W8 -> FStar.Int8.(x - y)
    | Signed W16 -> FStar.Int16.(x - y)
    | Signed W32 -> FStar.Int32.(x - y)
    | Signed W64 -> FStar.Int64.(x - y)
    | Signed W128 -> FStar.Int128.(x - y)

(*| Overloaded unsigned subtraction with no precondition whose result is only
    specified when it does not underflow.

    Only for unsigned fixed widths; unfolds to the `sub_underspec` of the
    underlying module. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( -? )
        (#sw:_{Unsigned? sw})
        (x:int_t sw)
        (y:int_t sw)
  : Tot (int_t sw)
  = let Unsigned w = sw in
    match w with
    | W8 -> FStar.UInt8.(x -?^ y)
    | W16 -> FStar.UInt16.(x -?^ y)
    | W32 -> FStar.UInt32.(x -?^ y)
    | W64 -> FStar.UInt64.(x -?^ y)
    | W128 -> FStar.UInt128.(x -?^ y)

(*| Overloaded wrapping subtraction for unsigned fixed widths:
    `v (x -% y) == (v x - v y) % pow2 n` for width `n`.

    No precondition. Unfolds to the `sub_mod` of the underlying module. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( -% )
         (#sw:_{Unsigned? sw})
         (x:int_t sw)
         (y:int_t sw)
  : Tot  (int_t sw)
  = let Unsigned w = sw in
    match w with
    | W8 -> FStar.UInt8.(x -%^ y)
    | W16 -> FStar.UInt16.(x -%^ y)
    | W32 -> FStar.UInt32.(x -%^ y)
    | W64 -> FStar.UInt64.(x -%^ y)
    | W128 -> FStar.UInt128.(x -%^ y)

(*| Overloaded negation for signed types, computed as `0 - x`.

    Requires `0 - v x` to be within bounds, which excludes the minimum value
    of a fixed width. Only for `Signed` widths, including `Signed Winfinite`. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( ~- )
         (#sw:_{Signed? sw})
         (x:int_t sw{within_bounds sw (0 - v x)})
  : Tot  (int_t sw)
  = let Signed w = sw in
    match w with
    | Winfinite -> 0 - x
    | W8 -> FStar.Int8.(0y - x)
    | W16 -> FStar.Int16.(0s - x)
    | W32 -> FStar.Int32.(0l - x)
    | W64 -> FStar.Int64.(0L - x)
    | W128 -> FStar.Int128.(int_to_t 0 - x)

(*| Overloaded multiplication without overflow, at any width except 128 bits.

    Requires the product to be within bounds
    (`FStar.Integers.within_bounds sw (v x * v y)`). For a concrete width it
    unfolds to the multiplication of the underlying module, whose contract
    gives `v (x * y) == v x * v y`. Neither `Unsigned W128` nor
    `Signed W128` is supported. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( * ) (#sw:signed_width{width_of_sw sw <> W128})
          (x:int_t sw)
          (y:int_t sw{within_bounds sw (v x * v y)})
  : Tot   (int_t sw)
  = match sw with
    | Signed Winfinite -> x * y
    | Unsigned W8 -> FStar.UInt8.(x * y)
    | Unsigned W16 -> FStar.UInt16.(x * y)
    | Unsigned W32 -> FStar.UInt32.(x * y)
    | Unsigned W64 -> FStar.UInt64.(x * y)
    | Signed W8 -> FStar.Int8.(x * y)
    | Signed W16 -> FStar.Int16.(x * y)
    | Signed W32 -> FStar.Int32.(x * y)
    | Signed W64 -> FStar.Int64.(x * y)
    | Signed W128 -> FStar.Int128.(x * y)

(*| Overloaded unsigned multiplication with no precondition whose result is
    only specified when it does not overflow.

    Only for unsigned widths of at most 64 bits; unfolds to the
    `mul_underspec` of the underlying module. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( *? ) (#sw:_{Unsigned? sw /\ width_of_sw sw <> W128})
           (x:int_t sw)
           (y:int_t sw)
  : Tot    (int_t sw)
  = let Unsigned w = sw in
    match w with
    | W8 -> FStar.UInt8.(x *?^ y)
    | W16 -> FStar.UInt16.(x *?^ y)
    | W32 -> FStar.UInt32.(x *?^ y)
    | W64 -> FStar.UInt64.(x *?^ y)

(*| Overloaded wrapping multiplication for unsigned widths of at most 64
    bits: `v (x *% y) == (v x * v y) % pow2 n` for width `n`.

    No precondition. Unfolds to the `mul_mod` of the underlying module. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( *% ) (#sw:_{Unsigned? sw /\ width_of_sw sw <> W128})
           (x:int_t sw)
           (y:int_t sw)
  : Tot    (int_t sw)
  = let Unsigned w = sw in
    match w with
    | W8 -> FStar.UInt8.(x *%^ y)
    | W16 -> FStar.UInt16.(x *%^ y)
    | W32 -> FStar.UInt32.(x *%^ y)
    | W64 -> FStar.UInt64.(x *%^ y)

(*| Overloaded strict greater-than test, at any width; returns
    `v x > v y`. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( > ) #sw (x:int_t sw) (y:int_t sw) : bool =
    match sw with
    | Signed Winfinite -> x > y
    | Unsigned W8 -> FStar.UInt8.(x > y)
    | Unsigned W16 -> FStar.UInt16.(x > y)
    | Unsigned W32 -> FStar.UInt32.(x > y)
    | Unsigned W64 -> FStar.UInt64.(x > y)
    | Unsigned W128 -> FStar.UInt128.(x > y)
    | Signed W8 -> FStar.Int8.(x > y)
    | Signed W16 -> FStar.Int16.(x > y)
    | Signed W32 -> FStar.Int32.(x > y)
    | Signed W64 -> FStar.Int64.(x > y)
    | Signed W128 -> FStar.Int128.(x > y)

(*| Overloaded greater-than-or-equal test, at any width; returns
    `v x >= v y`. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( >= ) #sw (x:int_t sw) (y:int_t sw) : bool =
    match sw with
    | Signed Winfinite -> x >= y
    | Unsigned W8 -> FStar.UInt8.(x >= y)
    | Unsigned W16 -> FStar.UInt16.(x >= y)
    | Unsigned W32 -> FStar.UInt32.(x >= y)
    | Unsigned W64 -> FStar.UInt64.(x >= y)
    | Unsigned W128 -> FStar.UInt128.(x >= y)
    | Signed W8 -> FStar.Int8.(x >= y)
    | Signed W16 -> FStar.Int16.(x >= y)
    | Signed W32 -> FStar.Int32.(x >= y)
    | Signed W64 -> FStar.Int64.(x >= y)
    | Signed W128 -> FStar.Int128.(x >= y)


(*| Overloaded strict less-than test, at any width; returns `v x < v y`. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( < ) #sw (x:int_t sw) (y:int_t sw) : bool =
    match sw with
    | Signed Winfinite -> x < y
    | Unsigned W8 -> FStar.UInt8.(x < y)
    | Unsigned W16 -> FStar.UInt16.(x < y)
    | Unsigned W32 -> FStar.UInt32.(x < y)
    | Unsigned W64 -> FStar.UInt64.(x < y)
    | Unsigned W128 -> FStar.UInt128.(x < y)
    | Signed W8 -> FStar.Int8.(x < y)
    | Signed W16 -> FStar.Int16.(x < y)
    | Signed W32 -> FStar.Int32.(x < y)
    | Signed W64 -> FStar.Int64.(x < y)
    | Signed W128 -> FStar.Int128.(x < y)

(*| Overloaded less-than-or-equal test, at any width; returns `v x <= v y`. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( <= ) #sw (x:int_t sw) (y:int_t sw) : bool =
    match sw with
    | Signed Winfinite -> x <= y
    | Unsigned W8 -> FStar.UInt8.(x <= y)
    | Unsigned W16 -> FStar.UInt16.(x <= y)
    | Unsigned W32 -> FStar.UInt32.(x <= y)
    | Unsigned W64 -> FStar.UInt64.(x <= y)
    | Unsigned W128 -> FStar.UInt128.(x <= y)
    | Signed W8 -> FStar.Int8.(x <= y)
    | Signed W16 -> FStar.Int16.(x <= y)
    | Signed W32 -> FStar.Int32.(x <= y)
    | Signed W64 -> FStar.Int64.(x <= y)
    | Signed W128 -> FStar.Int128.(x <= y)

(*| Overloaded division, at any width except `Unsigned W128`.

    Requires a non-zero divisor and, for signed types, a quotient within
    bounds (this excludes the minimum value divided by `-1`). The rounding
    depends on the type: unsigned division rounds down, fixed-width signed
    division truncates towards zero (`FStar.Int.op_Slash_Minus`), and on
    `Signed Winfinite` it is `Prims.op_Division`, which is Euclidean. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( / ) (#sw:signed_width{sw <> Unsigned W128})
          (x:int_t sw)
          (y:int_t sw{0 <> (v y <: Prims.int) /\
                      (match sw with
                       | Unsigned _ -> within_bounds sw (v x / v y)
                       | Signed _ -> within_bounds sw (v x `FStar.Int.op_Slash_Minus` v y))})
   : Tot (int_t sw)
   = match sw with
     | Signed Winfinite -> x / y
     | Unsigned W8 -> FStar.UInt8.(x / y)
     | Unsigned W16 -> FStar.UInt16.(x / y)
     | Unsigned W32 -> FStar.UInt32.(x / y)
     | Unsigned W64 -> FStar.UInt64.(x / y)
     | Signed W8 -> FStar.Int8.(x / y)
     | Signed W16 -> FStar.Int16.(x / y)
     | Signed W32 -> FStar.Int32.(x / y)
     | Signed W64 -> FStar.Int64.(x / y)
     | Signed W128 -> FStar.Int128.(x / y)

(*| Overloaded remainder, at any width except `Unsigned W128`.

    Requires a non-zero divisor and a quotient within bounds. The result
    follows the type: `FStar.UInt.mod` for unsigned widths,
    `FStar.Int.mod` (same sign as the dividend) for fixed-width signed
    types, and `Prims.op_Modulus` (always non-negative) on
    `Signed Winfinite`. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( % ) (#sw:signed_width{sw <> Unsigned W128})
          (x:int_t sw)
          (y:int_t sw{0 <> (v y <: Prims.int) /\
                      (match sw with
                       | Unsigned _ -> within_bounds sw (FStar.UInt.mod #(nat_of_fixed_width (width_of_sw sw)) (v x) (v y))
                       | Signed Winfinite -> True
                       | Signed _ -> within_bounds sw (FStar.Int.mod #(nat_of_fixed_width (width_of_sw sw)) (v x) (v y))) /\
                       within_bounds sw (FStar.Int.op_Slash_Minus (v x) (v y))})
   : Tot (int_t sw)
   = match sw with
     | Signed Winfinite -> x % y
     | Unsigned W8 -> FStar.UInt8.(x % y)
     | Unsigned W16 -> FStar.UInt16.(x % y)
     | Unsigned W32 -> FStar.UInt32.(x % y)
     | Unsigned W64 -> FStar.UInt64.(x % y)
     | Signed W8 -> FStar.Int8.(x % y)
     | Signed W16 -> FStar.Int16.(x % y)
     | Signed W32 -> FStar.Int32.(x % y)
     | Signed W64 -> FStar.Int64.(x % y)
     | Signed W128 -> FStar.Int128.(x % y)

(*| Overloaded bitwise exclusive or, for fixed widths only.

    Unfolds to the `logxor` of the underlying module. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( ^^ ) #sw (x:int_t sw) (y:int_t sw{width_of_sw sw <> Winfinite})
    : Tot (int_t sw)
    = match sw with
      | Unsigned W8 -> FStar.UInt8.(x ^^ y)
      | Unsigned W16 -> FStar.UInt16.(x ^^ y)
      | Unsigned W32 -> FStar.UInt32.(x ^^ y)
      | Unsigned W64 -> FStar.UInt64.(x ^^ y)
      | Unsigned W128 -> FStar.UInt128.(x ^^ y)
      | Signed W8 -> FStar.Int8.(x ^^ y)
      | Signed W16 -> FStar.Int16.(x ^^ y)
      | Signed W32 -> FStar.Int32.(x ^^ y)
      | Signed W64 -> FStar.Int64.(x ^^ y)
      | Signed W128 -> FStar.Int128.(x ^^ y)

(*| Overloaded bitwise and, for fixed widths only.

    Unfolds to the `logand` of the underlying module. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( &^ ) #sw (x:int_t sw) (y:int_t sw{width_of_sw sw <> Winfinite})
    : Tot (int_t sw)
    = match sw with
      | Unsigned W8 -> FStar.UInt8.(x &^ y)
      | Unsigned W16 -> FStar.UInt16.(x &^ y)
      | Unsigned W32 -> FStar.UInt32.(x &^ y)
      | Unsigned W64 -> FStar.UInt64.(x &^ y)
      | Unsigned W128 -> FStar.UInt128.(x &^ y)
      | Signed W8 -> FStar.Int8.(x &^ y)
      | Signed W16 -> FStar.Int16.(x &^ y)
      | Signed W32 -> FStar.Int32.(x &^ y)
      | Signed W64 -> FStar.Int64.(x &^ y)
      | Signed W128 -> FStar.Int128.(x &^ y)

(*| Overloaded bitwise or, for fixed widths only.

    Unfolds to the `logor` of the underlying module. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( |^ ) #sw (x:int_t sw) (y:int_t sw{width_of_sw sw <> Winfinite})
    : Tot (int_t sw)
    = match sw with
      | Unsigned W8 -> FStar.UInt8.(x |^ y)
      | Unsigned W16 -> FStar.UInt16.(x |^ y)
      | Unsigned W32 -> FStar.UInt32.(x |^ y)
      | Unsigned W64 -> FStar.UInt64.(x |^ y)
      | Unsigned W128 -> FStar.UInt128.(x |^ y)
      | Signed W8 -> FStar.Int8.(x |^ y)
      | Signed W16 -> FStar.Int16.(x |^ y)
      | Signed W32 -> FStar.Int32.(x |^ y)
      | Signed W64 -> FStar.Int64.(x |^ y)
      | Signed W128 -> FStar.Int128.(x |^ y)

(*| Overloaded left shift of a non-negative integer by a `uint_32` amount
    smaller than the width, for fixed widths only.

    For unsigned types the bits shifted out are lost (the result is
    `(v x * pow2 (v y)) % pow2 n`). For signed types the shifted value must
    remain within bounds. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( <<^ ) #sw (x:int_t sw{0 <= v x})
                (y:int_t (Unsigned W32){width_of_sw sw <> Winfinite /\ v y < nat_of_fixed_width (width_of_sw sw) /\ (Signed? sw ==> within_bounds sw (v x * pow2 (v y)))})
    : Tot (int_t sw)
    = match sw with
      | Unsigned W8 -> FStar.UInt8.(x <<^ y)
      | Unsigned W16 -> FStar.UInt16.(x <<^ y)
      | Unsigned W32 -> FStar.UInt32.(x <<^ y)
      | Unsigned W64 -> FStar.UInt64.(x <<^ y)
      | Unsigned W128 -> FStar.UInt128.(x <<^ y)
      | Signed W8 -> FStar.Int8.(x <<^ y)
      | Signed W16 -> FStar.Int16.(x <<^ y)
      | Signed W32 -> FStar.Int32.(x <<^ y)
      | Signed W64 -> FStar.Int64.(x <<^ y)
      | Signed W128 -> FStar.Int128.(x <<^ y)

(*| Overloaded right shift of a non-negative integer by a `uint_32` amount
    smaller than the width, for fixed widths only; the result is
    `v x / pow2 (v y)`. *)
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( >>^ ) #sw (x:int_t sw{0 <= v x})
                (y:int_t (Unsigned W32){width_of_sw sw <> Winfinite /\ v y < nat_of_fixed_width (width_of_sw sw)})
    : Tot (int_t sw)
    = match sw with
      | Unsigned W8 -> FStar.UInt8.(x >>^ y)
      | Unsigned W16 -> FStar.UInt16.(x >>^ y)
      | Unsigned W32 -> FStar.UInt32.(x >>^ y)
      | Unsigned W64 -> FStar.UInt64.(x >>^ y)
      | Unsigned W128 -> FStar.UInt128.(x >>^ y)
      | Signed W8 -> FStar.Int8.(x >>^ y)
      | Signed W16 -> FStar.Int16.(x >>^ y)
      | Signed W32 -> FStar.Int32.(x >>^ y)
      | Signed W64 -> FStar.Int64.(x >>^ y)
      | Signed W128 -> FStar.Int128.(x >>^ y)

(*| Unsigned 8-bit integers, `FStar.UInt8.t`, as an index of this module. *)
[@@mark_for_norm]
unfold
let uint_8   = int_t (Unsigned W8)

(*| Unsigned 16-bit integers, `FStar.UInt16.t`, as an index of this module. *)
[@@mark_for_norm]
unfold
let uint_16  = int_t (Unsigned W16)

(*| Unsigned 32-bit integers, `FStar.UInt32.t`, as an index of this module. *)
[@@mark_for_norm]
unfold
let uint_32  = int_t (Unsigned W32)

(*| Unsigned 64-bit integers, `FStar.UInt64.t`, as an index of this module. *)
[@@mark_for_norm]
unfold
let uint_64  = int_t (Unsigned W64)

(*| Mathematical integers (`Signed Winfinite`), equal to `Prims.int`.

    Opening `FStar.Integers` shadows `Prims.int` with this name; the two are
    the same type. *)
[@@mark_for_norm]
unfold
let int       = int_t (Signed Winfinite)

(*| Signed 8-bit integers, `FStar.Int8.t`, as an index of this module. *)
[@@mark_for_norm]
unfold
let int_8   = int_t (Signed W8)

(*| Signed 16-bit integers, `FStar.Int16.t`, as an index of this module. *)
[@@mark_for_norm]
unfold
let int_16  = int_t (Signed W16)

(*| Signed 32-bit integers, `FStar.Int32.t`, as an index of this module. *)
[@@mark_for_norm]
unfold
let int_32  = int_t (Signed W32)

(*| Signed 64-bit integers, `FStar.Int64.t`, as an index of this module. *)
[@@mark_for_norm]
unfold
let int_64  = int_t (Signed W64)

(*| Signed 128-bit integers, `FStar.Int128.t`, as an index of this module. *)
[@@mark_for_norm]
unfold
let int_128 = int_t (Signed W128)

(*| Holds when applying the mathematical operation `op` to the values of `x`
    and `y` gives a result within the bounds of their type.

    Convenient as a precondition of the non-wrapping operators, as in
    `y:uint_8{ok (+) x y}`. *)
[@@mark_for_norm]
unfold
let ok #sw
       (op:(int_t (Signed Winfinite)
          -> int_t (Signed Winfinite)
          -> int_t (Signed Winfinite)))
       (x:int_t sw)
       (y:int_t sw)
   = within_bounds sw (op (v x) (v y))

(*| Non-negative integers, as a refinement of `FStar.Integers.int`; the same
    as `Prims.nat`. *)
[@@mark_for_norm]
unfold
let nat = i:int{ i >= 0 }

(*| Positive integers, as a refinement of `FStar.Integers.nat`; the same as
    `Prims.pos`. *)
[@@mark_for_norm]
unfold
let pos = i:nat{ 0 < i }

////////////////////////////////////////////////////////////////////////////////
//Test
////////////////////////////////////////////////////////////////////////////////
(*| Test: overloaded addition on `FStar.Integers.int`. *)
let f_int (x:int) (y:int) = x + y
(*| Test: overloaded addition on `FStar.Integers.nat`. *)
let f_nat (x:nat) (y:nat) = x + y
(*| Test: overloaded addition mixing `nat`, `int` and `pos` arguments. *)
let f_nat_int_pos (x:nat) (y:int) (z:pos) = x + y + z
(*| Test: overloaded addition on `uint_8` under an `FStar.Integers.ok`
    precondition. *)
let f_uint_8 (x:uint_8) (y:uint_8{ok (+) x y}) = x + y
(*| Test: overloaded addition on `int_16` under an `FStar.Integers.ok`
    precondition. *)
let f_int_16 (x:int_16) (y:int_16{ok (+) x y}) = x + y
(*| Test: computes `x + y * y` on `uint_32`, with `FStar.Integers.ok`
    preconditions for both operations. *)
let g (x:uint_32) (y:uint_32{ok ( * ) y y /\ ok (+) x (y * y)}) = x + y * y
(*| Test: adds two `Prims.nat` values after converting them with
    `FStar.Integers.u`. *)
let h (x:Prims.nat) (y:Prims.nat): nat  = u x + u y
(*| Test: overloaded addition on `Prims.nat` arguments. *)
let i (x:Prims.nat) (y:Prims.nat) = x + y
(*| Test: overloaded subtraction on `Prims.int` and `Prims.nat` arguments. *)
let j (x:Prims.int) (y:Prims.nat) = x - y
(*| Test: overloaded multiplication on `Prims.int` arguments. *)
let k (x:Prims.int) (y:Prims.int) = x * y
