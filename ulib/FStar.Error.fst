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
/// A library for optional results,
/// where the error case carries some payload
module FStar.Error

(*| An optional result whose failure case carries a payload: `Error e` with `e: 'a`, or `Correct v` with `v: 'b`.

    Compare `FStar.Pervasives.result`, whose error case carries an exception.
    `FStar.Error.invertOptResult` lets the SMT solver case-split on it. *)
type optResult 'a 'b =
  | Error of 'a
  | Correct of 'b

(*| States that every `optResult a b` is either `Error?` or `Correct?`.

    Proved with `allow_inversion`, it allows inverting `optResult` without
    raising the global inductive fuel. Triggered automatically on the type
    `optResult a b`. *)
let invertOptResult (a:Type) (b:Type)
  : Lemma
    (requires True)
    (ensures (forall (x:optResult a b). Error? x \/ Correct? x))
    [SMTPat (optResult a b)]
  = allow_inversion (optResult a b)

(*| Builds an error message from a source file name, a line number and a text; it returns `text` unchanged.

    The `file` and `line` arguments are currently ignored. The definition is
    `irreducible`, so the equation `perror file line text == text` is not
    available to proofs. *)
irreducible
let perror
    (file:string)
    (line:int)
    (text:string)
  : Tot string
  = text

(*| Wraps a value as a successful result: `correct x == Correct x`.

    ```fstar
    let safe_head (l: list int) : FStar.Error.optResult string int =
      match l with
      | [] -> FStar.Error.Error "empty list"
      | x :: _ -> FStar.Error.correct x
    ``` *)
let correct
    (#a:Type)
    (#r:Type)
    (x:r)
  : Tot (optResult a r)
  = Correct x

(*| Marks code that should never run, without proving it unreachable.

    `Div` effect with a trivial precondition, so it can be called anywhere.
    When executed it prints `s` with `FStar.IO.debug_print_string` and then
    loops forever; it does not raise. Prefer `FStar.Error.unreachable` when
    the call site can be proved dead, which matters when dynamic errors are
    security-critical. *)
let rec unexpected
    (#a:Type)
    (s:string)
   : Div a
     (requires True)
     (ensures (fun _ -> True))
   = let _ = FStar.IO.debug_print_string ("Platform.Error.unexpected: " ^ s) in
     unexpected s

(*| Marks code that is proved never to run.

    `Div` effect with precondition `False`, so typechecking a call obliges the
    caller to prove that the call site is unreachable. If it were executed it
    would print `s` with `FStar.IO.debug_print_string` and loop forever. See
    `FStar.Error.unexpected` for the unchecked variant. *)
let rec unreachable
    (#a:Type)
    (s:string)
   : Div a
     (requires False)
     (ensures (fun _ -> False))
   = let _ = FStar.IO.debug_print_string ("Platform.Error.unreachable: " ^ s) in
     unreachable s

(*| Selects between an ideal and a real computation; it returns the real value `x` and ignores `f`.

    The definition is `irreducible`, so proofs cannot see that the result is
    `x`. *)
irreducible
let if_ideal
    (f:unit -> Tot 'a)
    (x:'a)
  : Tot 'a
  = x
