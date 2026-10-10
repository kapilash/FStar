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
module FStar.Printf

(*
 * A variable arity C-style printf
 * See tests/micro-benchmarks/Test.Printf.fst for example usage
 *)

open FStar.Char
open FStar.String

(*| A user-defined format argument: a type `a` together with a total printer `f` of type `a -> string`.

    Built with the constructor `MkExtension`; used with `FStar.Printf.ext_sprintf`
    and an `FStar.Printf.extension_parser` for `%X` specifiers. Equality is not
    decidable (`noeq`). *)
noeq
type extension =
  | MkExtension : #a:Type0 -> $f:(a -> Tot string) -> extension

(*| The kinds of argument a format string can take, one constructor per specifier.

    - `Bool` is `%b`, for `bool`.
    - `Int` is `%d`, for `int`.
    - `Char` is `%c`, for `char`.
    - `String` is `%s`, for `string`.
    - `U8`, `U16`, `U32` and `U64` are `%uy`, `%us`, `%ul` and `%uL`, for `FStar.UInt8.t` to `FStar.UInt64.t`.
    - `I8`, `I16`, `I32` and `I64` are `%y`, `%i`, `%l` and `%L`, for `FStar.Int8.t` to `FStar.Int64.t`.
    - `Extension e` is a user extension, introduced by `%X`.

    The type of each argument is given by `FStar.Printf.arg_type`. Equality is
    not decidable (`noeq`). *)
noeq
type arg =
  | Bool
  | Int
  | Char
  | String
  | U8
  | U16
  | U32
  | U64
  | I8
  | I16
  | I32
  | I64
  | Extension of extension

(*| The F\* type of the value expected for a format argument kind; for `Extension (MkExtension #t f)` it is `t`. *)
let arg_type (a:arg) : Tot Type0 =
  match a with
  | Bool   -> bool
  | Int    -> int
  | Char   -> char
  | String -> string
  | U8     -> FStar.UInt8.t
  | U16    -> FStar.UInt16.t
  | U32    -> FStar.UInt32.t
  | U64    -> FStar.UInt64.t
  | I8     -> FStar.Int8.t
  | I16    -> FStar.Int16.t
  | I32    -> FStar.Int32.t
  | I64    -> FStar.Int64.t
  | Extension (MkExtension #t _)  -> t

(*| Prints a format argument: with the `to_string` function of its type, as the string itself for `String`, or with the extension's printer.

    For example, a `U32` argument is printed with `FStar.UInt32.to_string`, an
    `Int` with `string_of_int` and a `Bool` with `string_of_bool`. *)
let string_of_arg (#a:arg) (x:arg_type a) : string =
    match a with
    | Bool   -> string_of_bool x
    | Int    -> string_of_int x
    | Char   -> string_of_char x
    | String -> x
    | U8     -> FStar.UInt8.to_string x
    | U16    -> FStar.UInt16.to_string x
    | U32    -> FStar.UInt32.to_string x
    | U64    -> FStar.UInt64.to_string x
    | I8     -> FStar.Int8.to_string x
    | I16    -> FStar.Int16.to_string x
    | I32    -> FStar.Int32.to_string x
    | I64    -> FStar.Int64.to_string x
    | Extension (MkExtension f) -> f x

(*| A directive of a parsed format string: `Lit c` for a literal character or `Arg a` for an argument. Internal to the module. *)
noeq
type dir =
  | Lit of char
  | Arg of arg

(*| The type of the printing function for a list of directives: one curried argument for each `Arg`, ending in `string`.

    `Lit` directives add no argument. *)
let rec dir_type (ds:list dir) : Tot Type0 =
  match ds with
  | [] -> string
  | Lit c :: ds' -> dir_type ds'
  | Arg a :: ds' -> arg_type a -> dir_type ds'

(*| Builds the printing function for a list of directives, in continuation-passing style.

    The continuation `k` accumulates the text formatted so far; start with the
    identity, as `FStar.Printf.sprintf` does. *)
let rec string_of_dirs
        (ds:list dir)
        (k:string -> string)
  : dir_type ds
  = match ds with
    | [] -> k ""
    | Lit c :: ds' ->
      coerce_eq () (
      string_of_dirs ds' (fun res -> k (string_of_char c ^ res))
      )
    | Arg a :: ds' ->
      fun (x : arg_type a) ->
        string_of_dirs ds' (fun res -> ((k "")
                                     ^ string_of_arg x
                                     ^ res))

(*| A parser for user format extensions: given the characters after `%X`, returns an extension and the remaining characters, or `None` if the input is not a valid extension.

    The remaining characters must be strictly smaller than the input, which
    ensures that `FStar.Printf.parse_format` terminates. *)
type extension_parser = i:list char -> option (extension & o:list char{o << i})

(*| Parses a format string, given as a list of characters, into directives; returns `None` if it is invalid.

    A `%` must be followed by one of `b`, `d`, `c`, `s`, `y`, `i`, `l`, `L`, by
    `u` and one of `y`, `s`, `l`, `L`, by `X` and an extension accepted by
    `parse_ext`, or by another `%` (a literal percent sign). Anything else after
    `%`, and a trailing `%`, makes the format invalid. Other characters are
    literals. *)
let rec parse_format
      (s:list char)
      (parse_ext: extension_parser)
    : option (list dir)
    = let add_dir (d:dir) (ods : option (list dir))
        : option (list dir)
        = match ods with
          | None -> None
          | Some ds -> Some (d::ds)
      in
      match s with
      | [] -> Some []
      | ['%'] -> None

      //Unsigned integers beging with '%u'
      | '%' :: 'u' :: s' -> begin
        match s' with
        | 'y' :: s'' -> add_dir (Arg U8) (parse_format s'' parse_ext)
        | 's' :: s'' -> add_dir (Arg U16) (parse_format s'' parse_ext)
        | 'l' :: s'' -> add_dir (Arg U32) (parse_format s'' parse_ext)
        | 'L' :: s'' -> add_dir (Arg U64) (parse_format s'' parse_ext)
        | _ -> None
        end

      //User extensions begin with '%X'
      | '%' :: 'X' :: s' -> begin
        match parse_ext s' with
        | Some (ext, rest) -> add_dir (Arg (Extension ext)) (parse_format rest parse_ext)
        | _ -> None
       end

      | '%' :: c :: s' -> begin
        match c with
        | '%' -> add_dir (Lit '%')    (parse_format s' parse_ext)
        | 'b' -> add_dir (Arg Bool)   (parse_format s' parse_ext)
        | 'd' -> add_dir (Arg Int)    (parse_format s' parse_ext)
        | 'c' -> add_dir (Arg Char)   (parse_format s' parse_ext)
        | 's' -> add_dir (Arg String) (parse_format s' parse_ext)
        | 'y' -> add_dir (Arg I8)     (parse_format s' parse_ext)
        | 'i' -> add_dir (Arg I16)    (parse_format s' parse_ext)
        | 'l' -> add_dir (Arg I32)    (parse_format s' parse_ext)
        | 'L' -> add_dir (Arg I64)    (parse_format s' parse_ext)
        | _   -> None
        end
      | c :: s' ->
        add_dir (Lit c) (parse_format s' parse_ext)

(*| Parses a format string into directives with `FStar.Printf.parse_format`; returns `None` if it is invalid. *)
let parse_format_string
    (s:string)
    (parse_ext:extension_parser)
  : option (list dir)
  = parse_format (list_of_string s) parse_ext

(*| The extension parser that accepts nothing, so `%X` is invalid; used by `FStar.Printf.sprintf`. *)
let no_extensions : extension_parser = fun s -> None

(*| Formats values according to a C-style format string; a variable-arity function returning a `string`.

    `sprintf s v1 ... vn` takes one argument for each specifier in `s`, with
    types given by `FStar.Printf.arg`. The format must be valid, which is
    checked by normalization when typechecking the call, so `s` should be a
    literal. Because `sprintf` is `inline_for_extraction` and its type and body
    are normalized, a call such as `sprintf "Hello %s" "world"` extracts to
    plain concatenation, `"Hello " ^ "world"`, with no runtime format parsing.

    ```fstar
    let greeting : string = FStar.Printf.sprintf "%s has %d items" "cart" 3

    let _ = assert_norm (greeting == "cart has 3 items")
    ```

    See `FStar.Printf.ext_sprintf` for user-defined specifiers. *)
inline_for_extraction
let sprintf
    (s:string{normalize_term (b2t (Some? (parse_format_string s no_extensions)))})
    : norm [unascribe; delta; iota; zeta; primops] (dir_type (Some?.v (parse_format_string s no_extensions)))
    = norm [unascribe; delta; iota; zeta; primops] (string_of_dirs (Some?.v (parse_format_string s no_extensions)) (fun s -> s))


(*| Like `FStar.Printf.sprintf`, with user-defined `%X` specifiers recognized by the given `FStar.Printf.extension_parser`. *)
inline_for_extraction
let ext_sprintf
    (parse_ext: extension_parser)
    (s:string{normalize_term (b2t (Some? (parse_format_string s parse_ext)))})
    : norm [unascribe; delta; iota; zeta; primops] (dir_type (Some?.v (parse_format_string s parse_ext)))
    = norm [unascribe; delta; iota; zeta; primops] (string_of_dirs (Some?.v (parse_format_string s parse_ext)) (fun s -> s))
