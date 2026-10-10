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
module FStar.IO

open FStar.All

exception EOF

(*| An abstract handle on an input channel, such as `FStar.IO.stdin` or a file opened with `FStar.IO.open_read_file`.

    A primitive type with no equality and no specification; it is realized by
    the target language's input channels. *)
new
val fd_read : Type0
(*| An abstract handle on an output channel, such as `FStar.IO.stdout` or a file opened with `FStar.IO.open_write_file`.

    A primitive type with no equality and no specification; it is realized by
    the target language's output channels. *)
new
val fd_write : Type0

(*| The standard input channel. An assumed primitive constant. *)
val stdin : fd_read
(*| The standard output channel. An assumed primitive constant.

    Write to it with `FStar.IO.write_string`; the `print` functions of this
    module also write to standard output. *)
val stdout : fd_write
(*| The standard error channel. An assumed primitive constant. *)
val stderr : fd_write

(*| Prints a newline to standard output.

    `ML` effect; nothing is specified about the output in the logic. *)
val print_newline : unit -> ML unit
(*| Prints a string to standard output, without a trailing newline.

    `ML` effect; nothing is specified about the output in the logic. For
    formatted output build the string with `FStar.Printf.sprintf`:

    ```fstar
    let hello () : FStar.All.ML unit =
      FStar.IO.print_string (FStar.Printf.sprintf "%ul\n" 42ul)
    ``` *)
val print_string : string -> ML unit

(* assume val print_nat_hex : nat -> ML unit *)
(* assume val print_nat_dec : nat -> ML unit *)

(* Print as hexadecimal with a leading 0x *)
(*| Prints a `FStar.UInt8.t` to standard output in hexadecimal, with a leading `0x` and no padding.

    `ML` effect with no postcondition: the output format is a property of the
    native realization, not of the specification. See
    `FStar.IO.print_uint8_hex_pad` for fixed-width output. *)
val print_uint8 : FStar.UInt8.t -> ML unit
(*| Prints a `FStar.UInt16.t` to standard output in hexadecimal, with a leading `0x` and no padding.

    `ML` effect with no postcondition: the output format is a property of the
    native realization, not of the specification. See
    `FStar.IO.print_uint16_hex_pad` for fixed-width output. *)
val print_uint16 : FStar.UInt16.t -> ML unit
(*| Prints a `FStar.UInt32.t` to standard output in hexadecimal, with a leading `0x` and no padding.

    `ML` effect with no postcondition: the output format is a property of the
    native realization, not of the specification. See
    `FStar.IO.print_uint32_hex_pad` for fixed-width output. *)
val print_uint32 : FStar.UInt32.t -> ML unit
(*| Prints a `FStar.UInt64.t` to standard output in hexadecimal, with a leading `0x` and no padding.

    `ML` effect with no postcondition: the output format is a property of the
    native realization, not of the specification. See
    `FStar.IO.print_uint64_hex_pad` for fixed-width output. *)
val print_uint64 : FStar.UInt64.t -> ML unit

(* Print as decimal *)
(*| Prints a `FStar.UInt8.t` to standard output in decimal, without padding.

    `ML` effect with no postcondition. See `FStar.IO.print_uint8_dec_pad` for
    zero-padded output. *)
val print_uint8_dec : FStar.UInt8.t -> ML unit
(*| Prints a `FStar.UInt16.t` to standard output in decimal, without padding.

    `ML` effect with no postcondition. See `FStar.IO.print_uint16_dec_pad` for
    zero-padded output. *)
val print_uint16_dec : FStar.UInt16.t -> ML unit
(*| Prints a `FStar.UInt32.t` to standard output in decimal, without padding.

    `ML` effect with no postcondition. See `FStar.IO.print_uint32_dec_pad` for
    zero-padded output. *)
val print_uint32_dec : FStar.UInt32.t -> ML unit
(*| Prints a `FStar.UInt64.t` to standard output in decimal, without padding.

    `ML` effect with no postcondition. See `FStar.IO.print_uint64_dec_pad` for
    zero-padded output. *)
val print_uint64_dec : FStar.UInt64.t -> ML unit

(* Print as hex in fixed width, no leading 0x *)
(*| Prints a `FStar.UInt8.t` to standard output in hexadecimal, zero-padded to 2 digits and without a leading `0x`.

    `ML` effect with no postcondition; the format is a property of the native
    realization. See `FStar.IO.print_uint8` for the `0x`-prefixed form. *)
val print_uint8_hex_pad : FStar.UInt8.t -> ML unit
(*| Prints a `FStar.UInt16.t` to standard output in hexadecimal, zero-padded to 4 digits and without a leading `0x`.

    `ML` effect with no postcondition; the format is a property of the native
    realization. See `FStar.IO.print_uint16` for the `0x`-prefixed form. *)
val print_uint16_hex_pad : FStar.UInt16.t -> ML unit
(*| Prints a `FStar.UInt32.t` to standard output in hexadecimal, zero-padded to 8 digits and without a leading `0x`.

    `ML` effect with no postcondition; the format is a property of the native
    realization. See `FStar.IO.print_uint32` for the `0x`-prefixed form. *)
val print_uint32_hex_pad : FStar.UInt32.t -> ML unit
(*| Prints a `FStar.UInt64.t` to standard output in hexadecimal, zero-padded to 16 digits and without a leading `0x`.

    `ML` effect with no postcondition; the format is a property of the native
    realization. See `FStar.IO.print_uint64` for the `0x`-prefixed form. *)
val print_uint64_hex_pad : FStar.UInt64.t -> ML unit

(* Print as decimal, zero padded to maximum possible length *)
(*| Prints a `FStar.UInt8.t` to standard output in decimal, zero-padded to the width of the largest value (3 digits).

    `ML` effect with no postcondition. See `FStar.IO.print_uint8_dec` for
    unpadded output. *)
val print_uint8_dec_pad : FStar.UInt8.t -> ML unit
(*| Prints a `FStar.UInt16.t` to standard output in decimal, zero-padded to the width of the largest value (5 digits).

    `ML` effect with no postcondition. See `FStar.IO.print_uint16_dec` for
    unpadded output. *)
val print_uint16_dec_pad : FStar.UInt16.t -> ML unit
(*| Prints a `FStar.UInt32.t` to standard output in decimal, zero-padded to the width of the largest value (10 digits).

    `ML` effect with no postcondition. See `FStar.IO.print_uint32_dec` for
    unpadded output. *)
val print_uint32_dec_pad : FStar.UInt32.t -> ML unit
(*| Prints a `FStar.UInt64.t` to standard output in decimal, zero-padded to the width of the largest value (20 digits).

    `ML` effect with no postcondition. See `FStar.IO.print_uint64_dec` for
    unpadded output. *)
val print_uint64_dec_pad : FStar.UInt64.t -> ML unit

(*| Prints an arbitrary value to standard output in a backend-specific representation.

    `ML` effect; the output format is not specified and need not be human
    readable. Use it only for debugging. *)
val print_any : 'a -> ML unit
(*| Reads a line from standard input.

    `ML` effect; the result is unspecified in the logic, and end of input or
    I/O errors raise an exception of the target runtime. *)
val input_line : unit -> ML string
(*| Reads an integer from standard input.

    `ML` effect; malformed input and end of input raise an exception of the
    target runtime. *)
val input_int : unit -> ML int
(*| Reads a floating-point number from standard input.

    `ML` effect; malformed input and end of input raise an exception of the
    target runtime. *)
val input_float : unit -> ML FStar.Float64.float64
(*| Opens the file with the given name for reading.

    `ML` effect; failure to open the file raises an exception of the target
    runtime. Close the handle with `FStar.IO.close_read_file`. *)
val open_read_file : string -> ML fd_read
(*| Opens the file with the given name for writing.

    `ML` effect; failure to open the file raises an exception of the target
    runtime. Close the handle with `FStar.IO.close_write_file`. *)
val open_write_file : string -> ML fd_write
(*| Closes an input channel opened with `FStar.IO.open_read_file`. `ML` effect. *)
val close_read_file : fd_read -> ML unit
(*| Closes an output channel opened with `FStar.IO.open_write_file`. `ML` effect. *)
val close_write_file : fd_write -> ML unit
(*| Reads the next line from an input channel.

    `ML` effect; raises the exception `FStar.IO.EOF` at the end of the input. *)
val read_line : fd_read -> ML string
(*| Writes a string to an output channel. `ML` effect. *)
val write_string : fd_write -> string -> ML unit

(*| Prints a string to standard output from pure code; an unsound escape hatch for printf-style debugging.

    Although it is `Tot`, it performs a side effect when executed. The result is
    an unspecified `bool` in the logic; at run time it is `false`. The result is
    a `bool` rather than `unit` so that extraction does not erase the call.
    Because the function is treated as pure, the compiler may reorder,
    duplicate or drop calls, so the order and number of messages is not
    guaranteed. *)
val debug_print_string : string -> Tot bool
