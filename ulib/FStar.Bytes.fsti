(*
   Copyright 2008-2017 Microsoft Research

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
(*
A standard library for manipulation of value bytes.

This model is realized by Bytes.bytes in OCaml and by
struct {uintX_t size; char *bytes} (or similar) in C.

This file is essentially a specialized version of FStar.Seq,
with lemmas and refinements taylored for typical operations on
bytes, and with support for machine integers and C-extractible versions
(which Seq does not provide.)

@summary Value bytes standard library
*)
module FStar.Bytes

module S = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Str = FStar.String

(*| Abbreviation for `FStar.UInt8.t`, the type of 8-bit unsigned machine integers. *)
unfold let u8 = U8.t
(*| Abbreviation for `FStar.UInt16.t`, the type of 16-bit unsigned machine integers. *)
unfold let u16 = U16.t
(*| Abbreviation for `FStar.UInt32.t`, the type of 32-bit unsigned machine integers; used for lengths and indices of `FStar.Bytes.bytes`. *)
unfold let u32 = U32.t

(*| The element type of `FStar.Bytes.bytes`: an alias of `FStar.UInt8.t`.

    The module's design notes say it is realized by `uint8_t` in C and by `int` in OCaml. *)
unfold type byte = u8

(*| Abstract type of immutable byte strings, with decidable equality.

    The length of a value is a `FStar.Bytes.u32` (`FStar.Bytes.len`), so every value has fewer than `pow2 32` bytes. Specifications reason about a value through its ghost model `FStar.Bytes.reveal`, a `FStar.Seq.Base.seq` of bytes. The type and all its operations are assumed: this interface has no F\* implementation, and the module's design notes say it is realized by a length and a byte pointer in C and by a string in OCaml.

    See also `FStar.Endianness` for a pure sequence-based model of byte encodings. *)
val bytes : t:Type0{hasEq t}
(*| Returns the number of bytes in a byte string, as a 32-bit unsigned integer.

    Assumed; `FStar.Bytes.length_reveal` relates it to the length of `FStar.Bytes.reveal`. See `FStar.Bytes.length` for the same quantity as a `nat`. *)
val len : bytes -> u32

(*| Returns the number of bytes in a byte string as a `nat`: `FStar.UInt32.v (FStar.Bytes.len b)`. *)
unfold let length b = FStar.UInt32.v (len b)

(*| Ghost view of a byte string as the sequence of its bytes.

    It is `GTot`, so it can be used only in specifications; the operations of this module are specified through it. `FStar.Bytes.hide` is its inverse. *)
val reveal:
    bytes
  -> GTot (S.seq byte)

(*| The ghost sequence `FStar.Bytes.reveal x` has length `FStar.Bytes.length x`.

    Triggered automatically on `FStar.Seq.Base.length (reveal x)` or on `len x`. *)
val length_reveal:
    x:bytes
  -> Lemma (ensures (S.length (reveal x) = length x))
          [SMTPatOr [[SMTPat (S.length (reveal x))];
                     [SMTPat (len x)]]]

(*| Ghost conversion from a byte sequence shorter than `pow2 32` to a byte string; the inverse of `FStar.Bytes.reveal`.

    It is `GTot`, so it can be used only in specifications. *)
val hide:
    s:S.seq byte{S.length s < pow2 32}
  -> GTot bytes

(*| `hide (reveal x) = x`: a byte string is determined by its ghost sequence of bytes.

    Triggered automatically on `reveal x`. *)
val hide_reveal:
    x:bytes
  -> Lemma (ensures (hide (reveal x) = x))
          [SMTPat (reveal x)]

(*| `reveal (hide s) == s` for every byte sequence `s` shorter than `pow2 32`.

    Triggered automatically on `hide s`. *)
val reveal_hide:
    x:S.seq byte{S.length x < pow2 32}
  -> Lemma (ensures (reveal (hide x) == x))
          [SMTPat (hide x)]

(*| Byte strings of length exactly `l`. *)
type lbytes (l:nat) = b:bytes{length b = l}
(*| Byte strings whose length is less than `pow2 k`. *)
type kbytes (k:nat) = b:bytes{length b < pow2 k}

(*| Byte strings whose length, as a `FStar.Bytes.u32`, is exactly `l`; the 32-bit counterpart of `FStar.Bytes.lbytes`. *)
let lbytes32 (l:UInt32.t) = b:bytes{len b = l}

(*| The byte string of length 0. Assumed; `FStar.Bytes.empty_unique` states that it is the only one. *)
val empty_bytes : lbytes 0
(*| Every byte string of length 0 is equal to `FStar.Bytes.empty_bytes`.

    Triggered automatically on `len b`. *)
val empty_unique:
    b:bytes
  -> Lemma (length b = 0 ==> b = empty_bytes)
    [SMTPat (len b)]

(*| Returns the byte at position `pos`, which must be less than `FStar.Bytes.length b`.

    The result is `FStar.Seq.Base.index (reveal b) (v pos)`. It is `Pure` with the bound on `pos` as a refinement, so an out-of-bounds read does not typecheck. Also available as the notation `b.[pos]`; see `FStar.Bytes.index` for a `nat` position. *)
val get:
    b:bytes
  -> pos:u32{U32.v pos < length b}
  -> Pure byte
    (requires True)
    (ensures (fun y -> y == S.index (reveal b) (U32.v pos)))

(*| Notation `b.[i]` for `FStar.Bytes.get b i`: the byte at 32-bit position `i`, which must be in bounds. *)
unfold let ( .[] ) = get

(*| Returns the byte at a `nat` position `i < length b`; same as `FStar.Bytes.get` after converting `i` with `FStar.UInt32.uint_to_t`. *)
unfold let index (b:bytes) (i:nat{i < length b}) = get b (U32.uint_to_t i)

(*| Extensional equality of byte strings: same length and the same byte at every position.

    The quantifier is triggered on `b1.[i]` and `b2.[i]`. Use `FStar.Bytes.extensionality` to turn it into `=`. *)
let equal b1 b2 =
  length b1 = length b2 /\
  (forall (i:u32{U32.v i < length b1}).{:pattern (b1.[i]); (b2.[i])} b1.[i] == b2.[i])

(*| Byte strings that are `FStar.Bytes.equal` (same length and same bytes) are equal. *)
val extensionality:
    b1:bytes
  -> b2:bytes
  -> Lemma (requires (equal b1 b2))
          (ensures (b1 = b2))

(** creating byte values **)
(*| Returns a byte string of length `len` in which every byte is `v`.

    Assumed. The refinement states each byte, with pattern `b.[i]`. See `FStar.Bytes.create_` for a `nat` length and `FStar.Bytes.init` for bytes computed from their position.

    ```fstar
    let zeros : FStar.Bytes.lbytes 3 = FStar.Bytes.create 3ul 0uy

    let _ = assert (FStar.Bytes.get zeros 1ul == 0uy)
    ``` *)
val create:
    len:u32
  -> v:byte
  -> b:lbytes (U32.v len){forall (i:u32{U32.(i < len)}).{:pattern b.[i]} b.[i] == v}

(*| Variant of `FStar.Bytes.create` taking the length as a `nat` that must fit in 32 bits. *)
unfold
let create_ (n:nat{FStar.UInt.size n U32.n}) v = create (U32.uint_to_t n) v

(*| Returns a byte string of length `len` whose byte at position `i` is `f i`.

    Assumed. The refinement states each byte, with pattern `b.[i]`. *)
val init:
    len:u32
  -> f:(i:u32{U32.(i < len)} -> byte)
  -> b:lbytes (U32.v len){forall (i:u32{U32.(i < len)}).{:pattern b.[i]} b.[i] == f i}

// this is a hack JROESCH
(*| Returns a byte string of length 1 built from the byte `b`.

    The interface specifies only the length of the result, not its content. *)
val abyte (b:byte) : lbytes 1
    (* admit () create 1ul b *)

(*| Returns a byte string of length 2 built from a pair of bytes.

    The interface specifies only the length of the result, not its content. *)
val twobytes (b:byte&byte) : lbytes 2
    // init 2ul (fun i -> if i = 0ul then fst b else snd b)

(** appending bytes **)
(*| Concatenates two byte strings; requires the total length to fit in 32 bits.

    It is `Pure`: the precondition `FStar.UInt.size (length b1 + length b2) 32` must be proved by the caller. The ghost model of the result is `FStar.Seq.Base.append (reveal b1) (reveal b2)`. Also available as the operator `@|`. *)
val append:
    b1:bytes
  -> b2:bytes
  -> Pure bytes
         (requires (UInt.size (length b1 + length b2) U32.n))
         (ensures (fun b -> reveal b == S.append (reveal b1) (reveal b2)))
(*| Infix notation `b1 @| b2` for `FStar.Bytes.append`; requires the total length to fit in 32 bits. *)
unfold let ( @| ) = append

(*| Returns the bytes of `b` from position `s` (inclusive) to `e` (exclusive); requires `s <= e <= length b`.

    The ghost model of the result is `FStar.Seq.Base.slice (reveal b) (v s) (v e)`. See `FStar.Bytes.sub` for a start and a length, and `FStar.Bytes.slice_` for `nat` bounds. *)
val slice:
    b:bytes
  -> s:u32
  -> e:u32{U32.(s <= e) /\ U32.v e <= length b}
  -> r:bytes{reveal r == Seq.slice (reveal b) (U32.v s) (U32.v e)}
(*| Variant of `FStar.Bytes.slice` taking `nat` bounds, with `s <= e <= length b`. *)
let slice_ b (s:nat) (e:nat{s <= e /\ e <= length b}) = slice b (U32.uint_to_t s) (U32.uint_to_t e)

(*| Returns the `l` bytes of `b` starting at position `s`; requires `v s + v l <= length b`.

    The ghost model of the result is `FStar.Seq.Base.slice (reveal b) (v s) (v s + v l)`. *)
val sub:
    b:bytes
  -> s:u32
  -> l:u32{U32.v s + U32.v l <= length b}
  -> r:bytes{reveal r == Seq.slice (reveal b) (U32.v s) (U32.v s + U32.v l)}

(*| Splits a byte string at position `k <= length b` into its first `k` bytes and the rest.

    The ghost models of the two parts are given by `FStar.Seq.Properties.split (reveal b) (v k)`. *)
val split:
    b:bytes
  -> k:u32{U32.v k <= length b}
  -> p:(bytes&bytes){
     let x, y = p in
     (reveal x, reveal y) == Seq.split (reveal b) (U32.v k)}

(*| Variant of `FStar.Bytes.split` taking a `nat` position.

    Unlike `FStar.Bytes.split`, it requires `k < length b` (strictly), so it cannot split at the end. *)
unfold let split_ b (k:nat{FStar.UInt.size k U32.n /\ k < length b}) = split b (U32.uint_to_t k)

(** Interpret a sequence of bytes as a mathematical integer encoded in big endian **)
(*| Holds when the natural number `n` is less than `pow2 (8 * k)`, that is, fits in `k` bytes. *)
let fits_in_k_bytes (n:nat) (k:nat) = FStar.UInt.size n (8 * k)
(*| Natural numbers that fit in `k` bytes, that is, are less than `pow2 (8 * k)`. *)
type uint_k (k:nat) = n:nat{fits_in_k_bytes n k}

(*| Returns a number of bytes `k >= 1` sufficient to represent the natural number `n`.

    Assumed. `FStar.Bytes.lemma_repr_bytes_values` gives its value for `n < pow2 64` and `FStar.Bytes.repr_bytes_size` states it is minimal, so it is the least positive number of bytes needed (1 for `n = 0`). *)
val repr_bytes:
    n:nat
  -> k:pos{fits_in_k_bytes n k}

(*| Gives the value of `repr_bytes n` for `n < pow2 64`: 1 for `n < 256`, 2 for `n < 65536`, and so on up to 8.

    Triggered automatically on `repr_bytes n`. For larger `n` it states nothing. *)
val lemma_repr_bytes_values:
    n:nat
  -> Lemma (ensures ( let k = repr_bytes n in
                     if n < 256 then k==1
                     else if n < 65536 then k==2
                     else if n < 16777216 then k==3
                     else if n < 4294967296 then k==4
                     else if n < 1099511627776 then k==5
                     else if n < 281474976710656 then k==6
                     else if n < 72057594037927936 then k==7
                     else if n < 18446744073709551616 then k==8
                     else True ))
          [SMTPat (repr_bytes n)]

(*| If `n` fits in `k` bytes then `repr_bytes n <= k`.

    Triggered automatically on `fits_in_k_bytes n k`. Note: for `k = 0` and `n = 0` this conflicts with `repr_bytes 0 >= 1`, so this assumed interface is inconsistent (it entails `False`); do not rely on it in that case. *)
val repr_bytes_size:
    k:nat
  -> n:uint_k k
  -> Lemma (ensures (repr_bytes n <= k))
          [SMTPat (fits_in_k_bytes n k)]

(*| Interprets a byte string as a natural number less than `pow2 (8 * length b)`.

    Assumed. The module notes describe the encoding as big-endian; the interface states only the bound and the round-trip lemmas `FStar.Bytes.int_of_bytes_of_int` and `FStar.Bytes.bytes_of_int_of_bytes`. See `FStar.Endianness.be_to_n` for a fully specified model. *)
val int_of_bytes:
    b:bytes
  -> Tot (uint_k (length b))

(*| Encodes the natural number `n` as a byte string of length `k`; requires `repr_bytes n <= k` and `k < pow2 32`.

    Assumed; the inverse of `FStar.Bytes.int_of_bytes` (see `FStar.Bytes.int_of_bytes_of_int`). *)
val bytes_of_int:
    k:nat
  -> n:nat{repr_bytes n <= k /\ k < pow2 32}
  -> lbytes k

(*| Decoding an encoding gives back the number: `int_of_bytes (bytes_of_int k n) == n` when `n` fits in `k <= 32` bytes.

    Triggered automatically on `bytes_of_int k n`. *)
val int_of_bytes_of_int:
  #k:nat{k <= 32}
  -> n:uint_k k
  -> Lemma (ensures (int_of_bytes (bytes_of_int k n) == n))
          [SMTPat (bytes_of_int k n)]

(*| Encoding a decoded byte string gives it back: `bytes_of_int (length b) (int_of_bytes b) == b` when `length b <= 32`.

    Triggered automatically on `int_of_bytes b`. *)
val bytes_of_int_of_bytes:
    b:bytes{length b <= 32}
  -> Lemma (ensures (bytes_of_int (length b) (int_of_bytes b) == b))
          [SMTPat (int_of_bytes b)]

//18-02-25 use [uint32] instead of [int32] etc?
(*| Interprets a byte string of at most 4 bytes as a `FStar.UInt32.t` whose value is `int_of_bytes b`. *)
val int32_of_bytes:
    b:bytes{length b <= 4}
  -> n:u32{U32.v n == int_of_bytes b}

(*| Interprets a byte string of at most 2 bytes as a `FStar.UInt16.t` whose value is `int_of_bytes b`. *)
val int16_of_bytes:
    b:bytes{length b <= 2}
  -> n:u16{U16.v n == int_of_bytes b}

(*| Interprets a byte string of exactly 1 byte as a `FStar.UInt8.t` whose value is `int_of_bytes b`. *)
val int8_of_bytes:
    b:bytes{length b = 1}
  -> n:u8{U8.v n = int_of_bytes b}

(*| Encodes a 32-bit unsigned integer as 4 bytes, equal to `bytes_of_int 4 (v n)`. *)
val bytes_of_int32:
    n:U32.t
  -> b:lbytes 4{b == bytes_of_int 4 (U32.v n)}

(*| Encodes a 16-bit unsigned integer as 2 bytes, equal to `bytes_of_int 2 (v n)`. *)
val bytes_of_int16:
    n:U16.t
  -> b:lbytes 2{b == bytes_of_int 2 (U16.v n)}

(*| Encodes an 8-bit unsigned integer as 1 byte, equal to `bytes_of_int 1 (v n)`. *)
val bytes_of_int8:
    n:U8.t
  -> b:lbytes 1{b == bytes_of_int 1 (U8.v n)}

////////////////////////////////////////////////////////////////////////////////
(*| Byte strings of length at least `n`. *)
type minbytes (n:nat) = b:bytes{length b >= n}

(*| Combines the first `n` bytes of two byte strings by exclusive-or, returning `n` bytes.

    Assumed. Both arguments must have at least `n` bytes. The interface specifies only the length of the result and the properties `FStar.Bytes.xor_commutative`, `FStar.Bytes.xor_append` and `FStar.Bytes.xor_idempotent`, not the individual bytes. See `FStar.Bytes.xor_` for a `nat` length. *)
val xor:
    n:u32
  -> b1:minbytes (U32.v n)
  -> b2:minbytes (U32.v n)
  -> b:bytes{len b = n}

(*| Variant of `FStar.Bytes.xor` taking the length as an implicit `nat` that must fit in 32 bits. *)
unfold let xor_ (#n:nat{FStar.UInt.size n U32.n}) (b1:minbytes n) (b2:minbytes n) = xor (U32.uint_to_t n) b1 b2

(*| `xor n b1 b2 == xor n b2 b1`.

    Triggered automatically on `xor n b1 b2`. *)
val xor_commutative:
    n:u32
  -> b1:minbytes (U32.v n)
  -> b2:minbytes (U32.v n)
  -> Lemma (ensures (xor n b1 b2 == xor n b2 b1))
          [SMTPat (xor n b1 b2)]

(*| `xor` distributes over concatenation: xoring `b1 @| b2` with `x1 @| x2` is xoring `b1` with `x1` and `b2` with `x2`, then concatenating, when the lengths of the corresponding parts agree. *)
val xor_append:
    b1:bytes
  -> b2:bytes{FStar.UInt.size (length b1 + length b2) U32.n}
  -> x1:bytes{len x1 = len b1}
  -> x2:bytes{len x2 = len b2}
  -> Lemma (ensures (xor U32.(len b1 + len b2)
                        (b1 @| b2)
                        (x1 @| x2)
                    ==
                    xor (len b1) b1 x1 @| xor (len b2) b2 x2))

(*| Xoring twice with the same byte string gives the original back: `xor n (xor n b1 b2) b2 == b1`.

    Both arguments must have length exactly `n`. *)
val xor_idempotent:
    n:u32
  -> b1:lbytes (U32.v n)
  -> b2:lbytes (U32.v n)
  -> Lemma (ensures (xor n (xor n b1 b2) b2 == b1))

(*| Encodes a string as UTF-8 bytes; the string must have at most `pow2 30` characters.

    Assumed. The interface states only that the result has at most `4 * FStar.String.length s` bytes. *)
val utf8_encode:
    s:string{Str.maxlen s (pow2 30)}
  -> b:bytes{length b <= 4 * Str.length s}

(*| Decodes UTF-8 bytes as a string, returning `None` on failure.

    Assumed. If the result is `Some s` then `utf8_encode s == m`; the interface does not say when `None` is returned. *)
val iutf8_opt:
    m:bytes
  -> (option (s:string{Str.maxlen s (pow2 30) /\ utf8_encode s == m}))

(*| Converts a string of hexadecimal digits to the string of the bytes they denote.

    Assumed and total in F\*; the interface gives no specification of the result, including for strings that are not valid hexadecimal. *)
val string_of_hex: string -> Tot string

// missing post on the length of the results (exact on constant arguments)
(*| Converts a string of hexadecimal digits to the bytes they denote.

    Assumed and total in F\*; the interface gives no specification of the result, not even its length, including for strings that are not valid hexadecimal. *)
val bytes_of_hex: string -> Tot bytes
(*| Returns the hexadecimal representation of the characters of a string.

    Assumed; the interface gives no specification of the result. *)
val hex_of_string: string -> Tot string
(*| Returns the hexadecimal representation of a byte string.

    Assumed; the interface gives no specification of the result. *)
val hex_of_bytes: bytes -> Tot string
(*| Returns a printable representation of a byte string, for debugging.

    Assumed; the interface gives no specification of the result. *)
val print_bytes: bytes -> Tot string
(*| Converts a string to a byte string.

    Assumed; the interface gives no specification of the result. *)
val bytes_of_string: string -> bytes //abytes
