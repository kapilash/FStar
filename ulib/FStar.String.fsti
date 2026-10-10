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
module FStar.String
open FStar.List.Tot
(* String is a primitive type in F*.

   Most of the functions in this interface have a special status in
   that they are:

   1. All the total functions in this module are handled by F*'s
      normalizers and can be reduced during typechecking

   2. All the total functions, plus two functions in the ML effect,
      have native OCaml implementations in FStar_String.ml

   These functions are, however, not suitable for use in Low* code,
   since many of them incur implicit allocations that must be garbage
   collected.

   For strings in Low*, see LowStar.String, LowStar.Literal etc.
*)

(*| The type of characters in strings, an alias for `FStar.Char.char`. *)
type char = FStar.Char.char

(*| Converts a string to the list of its characters, in order.

    A primitive: it has no definition in F\*, but F\*'s normalizer can
    evaluate it on literals. Its inverse is `FStar.String.string_of_list`, as
    stated by the assumed lemmas `FStar.String.string_of_list_of_string` and
    `FStar.String.list_of_string_of_list`. The length of a string,
    `FStar.String.strlen`, is defined as the length of this list.

    ```fstar
    let _ = assert_norm (FStar.String.list_of_string "ab" == ['a'; 'b'])
    ``` *)
val list_of_string : string -> Tot (list char)

(*| Builds a string from a list of characters, in order.

    A primitive: it has no definition in F\*, but F\*'s normalizer can
    evaluate it. The inverse of `FStar.String.list_of_string`; see
    `FStar.String.list_of_string_of_list` and
    `FStar.String.string_of_list_of_string`. *)
val string_of_list : list char -> Tot string

(*| Converting a string to a list of characters and back gives the original
    string.

    Assumed, not proved: strings are primitive and have no model in F\*. *)
val string_of_list_of_string (s:string)
  : Lemma (string_of_list (list_of_string s) == s)

(*| Converting a list of characters to a string and back gives the original
    list.

    Assumed, not proved: strings are primitive and have no model in F\*. *)
val list_of_string_of_list (l:list char)
  : Lemma (list_of_string (string_of_list l) == l)

(*| The number of characters in a string, defined as the length of
    `FStar.String.list_of_string s`.

    It counts `FStar.Char.char` values, not bytes of an encoding. On a literal
    it can be computed by normalization:

    ```fstar
    let _ = assert_norm (FStar.String.strlen "hello" == 5)
    ``` *)
let strlen s = List.length (list_of_string s)

(*| An alias for `FStar.String.strlen`, unfolded eagerly. *)
unfold
let length s = strlen s

(*| States that `strlen s <= n`, in a form that is discharged by normalization
    when `s` is a literal.

    When `s` is a literal of at most `n` characters, the left disjunct reduces
    to `True` before the query reaches the SMT solver. Otherwise the right
    disjunct `FStar.String.strlen s <= n` remains, so the fact is still
    available in the context. *)
unfold
let maxlen s n = b2t (normalize_term (strlen s <= n)) \/ strlen s <= n

(*| Builds a string of length `l` by repeating a given character.

    The interface specifies only the length of the result. The intent is that
    every character is the given one, but no lemma states it. *)
val make: l:nat -> char -> Tot (s:string {length s = l})

(*| The one-character string made of `c`, defined as `FStar.String.make 1 c`.

    As for `FStar.String.make`, only the length of the result is specified. *)
let string_of_char (c:char) : Tot string = make 1 c

(*| Splits a string at every occurrence of any of the delimiter characters in
    the first argument.

    A primitive with no specification: the interface gives no lemma about
    the result, including how empty pieces are handled. *)
val split:   list char -> string -> Tot (list string)

(*| Concatenates a list of strings, inserting the separator `s` between
    consecutive elements.

    A primitive with no specification: no lemma relates the result to its
    arguments. For the concatenation of two strings, use the primitive `^`,
    which is described by `FStar.String.concat_length` and
    `FStar.String.list_of_concat`. *)
val concat:  string -> list string -> Tot string

(*| Compares two strings, intended as a lexicographic ordering.

    By convention the result is negative if the first string is smaller,
    zero if they are equal and positive otherwise. This is not specified: the
    interface states no property of the result, and does not fix the order on
    characters used. *)
val compare: string -> string -> Tot int

(*| Converts a string to lowercase, character by character.

    A primitive with no specification: the interface does not state which
    characters are affected or that the length is preserved. See also
    `FStar.Char.lowercase`. *)
val lowercase:  string -> Tot string

(*| Converts a string to uppercase, character by character.

    A primitive with no specification: the interface does not state which
    characters are affected or that the length is preserved. See also
    `FStar.Char.uppercase`. *)
val uppercase:  string -> Tot string

(*| Returns the character at position `n` of `s`, counting from 0.

    The precondition `n < length s` makes it total. It agrees with indexing
    the character list: see `FStar.String.index_list_of_string` and
    `FStar.String.index_string_of_list`. For an unchecked variant, see
    `FStar.String.get`. *)
val index: s:string -> n:nat {n < length s} -> Tot char

(*| Returns the position of the first occurrence of character `c` in string
    `s`, or `-1` if `c` does not occur.

    This behavior is not specified: the interface states no property of the
    result. *)
val index_of: string -> char -> Tot int

(*| Returns the substring of `s` of length `l` that starts at position `i`.

    The third argument is a length, not an end position. The interface
    specifies only the length of the result, not its characters. For a
    variant without static bounds, see `FStar.String.substring`. *)
val sub: s:string -> i:nat -> l:nat{i + l <= length s} -> Tot (r: string {length r = l})

(*| Maps `f` over the characters of `s` from left to right and concatenates
    the resulting strings.

    Runs in the `ML` effect and has no specification. Deprecated: define it
    with `FStar.String.list_of_string` and `FStar.List.collect` instead. *)
[@@(deprecated "FStar.String.collect can be defined using list_of_string and List.collect")]
val collect: (char -> FStar.All.ML string) -> string -> FStar.All.ML string

(*| Returns the substring of `s` of length `len` that starts at position `i`,
    without static bounds checks.

    A partial variant of `FStar.String.sub` in the `Ex` effect: it may raise
    an exception when the range is out of bounds. The third argument is a
    length, not an end position. The result is not specified. *)
val substring: string -> int -> int -> Ex string

(*| Returns the character at position `i` of `s`, without a static bounds
    check.

    A partial variant of `FStar.String.index` in the `Ex` effect: it may
    raise an exception when `i` is out of bounds. The result is not
    specified. *)
val get: string -> int -> Ex char


/// Some lemmas (admitted for now as we don't have a model)
(*| The length of the concatenation `s1 ^ s2` is the sum of the lengths of
    `s1` and `s2`.

    Assumed, not proved: strings are primitive and have no model in F\*.
    Not an SMT pattern; call it explicitly:

    ```fstar
    let concat_len (s1 s2: string)
      : Lemma (FStar.String.strlen (s1 ^ s2) = FStar.String.strlen s1 + FStar.String.strlen s2)
      = FStar.String.concat_length s1 s2
    ``` *)
val concat_length (s1 s2: string): Lemma
  (ensures length (s1 ^ s2) = length s1 + length s2)

(*| The characters of `s1 ^ s2` are those of `s1` followed by those of `s2`.

    Assumed, not proved: strings are primitive and have no model in F\*. *)
val list_of_concat (s1 s2: string): Lemma
  (ensures list_of_string (s1 ^ s2) == list_of_string s1 @ list_of_string s2)

(*| The character at position `i` of `string_of_list l` is the element at
    position `i` of `l`.

    Assumed, not proved. The precondition uses
    `FStar.String.list_of_string_of_list` to relate the two lengths. *)
val index_string_of_list (l:list char) (i : nat{i < List.Tot.length l}) :
  Lemma (
    (**) list_of_string_of_list l; // necessary to get equality between the lengths
    index (string_of_list l) i == List.Tot.index l i)

(*| The element at position `i` of `list_of_string s` is the character
    `index s i`.

    Proved from `FStar.String.index_string_of_list` and
    `FStar.String.string_of_list_of_string`. *)
let index_list_of_string (s:string) (i : nat{i < length s}) :
  Lemma (List.Tot.index (list_of_string s) i == index s i) =
  index_string_of_list (list_of_string s) i;
  string_of_list_of_string s

(*| Concatenation of strings is injective when one of the two pairs of parts
    has equal lengths.

    If `s0 ^ s1 == s0' ^ s1'` and either `length s0 == length s0'` or
    `length s1 == length s1'`, then `s0 == s0'` and `s1 == s1'`. Proved from
    `FStar.String.list_of_concat` and `FStar.List.Tot.Properties.append_injective`. *)
let concat_injective (s0 s0':string)
                     (s1 s1':string)
  : Lemma
    (s0 ^ s1 == s0' ^ s1' /\
     (length s0 == length s0' \/
      length s1 == length s1') ==>
     s0 == s0' /\ s1 == s1')
  = list_of_concat s0 s1;
    list_of_concat s0' s1';
    append_injective (list_of_string s0)
                     (list_of_string s0')
                     (list_of_string s1)
                     (list_of_string s1');
    string_of_list_of_string s0;
    string_of_list_of_string s0';
    string_of_list_of_string s1;
    string_of_list_of_string s1'
