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

module FStar.Char

/// This module provides the [char] type, an abstract type
/// representing UTF-8 characters.
///
/// UTF-8 characters are representing in a variable-length encoding of
/// between 1 and 4 bytes, with a maximum of 21 bits used to represent
/// a code.
///
/// See https://en.wikipedia.org/wiki/UTF-8 and
/// https://erratique.ch/software/uucp/doc/unicode.html

module U32 = FStar.UInt32

(*| The primitive, abstract type of characters, with decidable equality.

    Each character has a numeric code, `FStar.Char.u32_of_char c`, in the
    range described by `FStar.Char.char_code`, and conversion back with
    `FStar.Char.char_of_u32` is a bijection. The interface fixes nothing else
    about characters, in particular no byte encoding. *)
new
val char:eqtype

(*| The numeric codes of characters: 32-bit unsigned integers `n` with
    `U32.v n < 0xd7ff`, or `0xe000 <= U32.v n <= 0x10ffff`.

    This excludes the UTF-16 surrogate range and values above `0x10ffff`, the
    largest Unicode code point. As written, the refinement also excludes
    `0xd7ff`. *)
type char_code = n: U32.t{U32.v n < 0xd7ff \/ (U32.v n >= 0xe000 /\ U32.v n <= 0x10ffff)}

(*| Returns the numeric code of a character.

    A primitive. Its inverse is `FStar.Char.char_of_u32`, as stated by the
    assumed lemmas `FStar.Char.char_of_u32_of_char` and
    `FStar.Char.u32_of_char_of_u32`. For the code as a `nat`, use
    `FStar.Char.int_of_char`. *)
val u32_of_char: char -> Tot char_code

(*| Returns the character with the given numeric code.

    A primitive. The inverse of `FStar.Char.u32_of_char`. For a code given as
    a `nat`, use `FStar.Char.char_of_int`. *)
val char_of_u32: char_code -> Tot char

(*| Converting a character to its code and back gives the original character.

    Assumed, not proved. Triggered automatically on `u32_of_char c`. *)
val char_of_u32_of_char (c: char)
    : Lemma (ensures (char_of_u32 (u32_of_char c) == c)) [SMTPat (u32_of_char c)]

(*| Converting a code to a character and back gives the original code.

    Assumed, not proved. Triggered automatically on `char_of_u32 c`. *)
val u32_of_char_of_u32 (c: char_code)
    : Lemma (ensures (u32_of_char (char_of_u32 c) == c)) [SMTPat (char_of_u32 c)]

(*| Returns the numeric code of a character as a natural number.

    Defined as `U32.v (u32_of_char c)`; see `FStar.Char.u32_of_char`. *)
let int_of_char (c: char) : nat = U32.v (u32_of_char c)

(*| Returns the character whose numeric code is the natural number `i`.

    The precondition is the range of `FStar.Char.char_code`. Defined with
    `FStar.Char.char_of_u32`. *)
let char_of_int (i: nat{i < 0xd7ff \/ (i >= 0xe000 /\ i <= 0x10ffff)}) : char = char_of_u32 (U32.uint_to_t i)

(*| Converts a character to lowercase.

    A primitive with no specification: the interface does not state which
    characters are affected. See also `FStar.Char.uppercase` and
    `FStar.String.lowercase`. *)
val lowercase: char -> Tot char

(*| Converts a character to uppercase.

    A primitive with no specification: the interface does not state which
    characters are affected. See also `FStar.Char.lowercase` and
    `FStar.String.uppercase`. *)
val uppercase: char -> Tot char

#set-options "--admit_smt_queries true"

(** This private primitive is used internally by the compiler to
    translate character literals with a desugaring-time check of the
    size of the number, rather than an expensive verification check.
    Since it is marked private, client programs cannot call it
    directly Since it is marked unfold, it eagerly reduces,
    eliminating the verification overhead of the wrapper *)

private unfold
let __char_of_int (x: int) : char = char_of_int x
#reset-options

