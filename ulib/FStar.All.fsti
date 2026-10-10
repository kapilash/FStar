(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.All

include FStar.Exn

(*| The abstract type of mutable references to values of type `a`, for use in the `ML` and `St` effects.

    There is no heap model: the operations `FStar.All.alloc`, `FStar.All.op_Bang`
    and `FStar.All.op_Colon_Equals` have no specification, so nothing can be
    proved about the contents of a reference. The type is realized by the native
    references of the target language. The parameter is marked strictly
    positive, so `ref` can appear in inductive type definitions. For verified
    stateful code use `FStar.ST` or `FStar.HyperStack.ST` instead. *)
new
val ref ([@@@ strictly_positive] a:Type0) : Type0

(*| Axiom that `ref a` is inhabited, for every `a`.

    It cannot be proved, because `FStar.All.alloc` is effectful; it is assumed
    of the native realization of references. It is needed to define top-level
    references, such as `let r : ref int = alloc 0`. Triggered automatically
    on `nonempty (ref a)`. *)
val nonempty_ref (a:Type0) : Lemma (nonempty (ref a)) [SMTPat (nonempty (ref a))]

(** References support decidable equality *)

(** STATE effect: underspecified state *)
assume effect STATE

assume sub_effect Div ~> STATE

effect St (a:Type) = STATE a

(*| Allocates a fresh reference holding the given value.

    `St` effect, underspecified: nothing is known about the result or the state
    afterwards. *)
val alloc : #a:Type0 -> a -> St (ref a)
(*| Reads the current contents of a reference.

    `St` effect, underspecified: the result is not related to earlier writes in
    the logic.

    ```fstar
    let counter_demo () : FStar.All.ML int =
      let r = FStar.All.alloc 0 in
      FStar.All.(r := !r + 1);
      FStar.All.(!r)
    ``` *)
val ( ! ) : #a:Type0 -> ref a -> St a
(*| Overwrites the contents of a reference.

    `St` effect, underspecified: the logic records nothing about the new
    contents. *)
val ( := ) : #a:Type0 -> ref a -> a -> St unit

(** ALL effect: combines state, exceptions and divergence *)
assume effect ALL

assume sub_effect EXN ~> ALL
assume sub_effect STATE ~> ALL

effect ML (a:Type) = ALL a

(*| Terminates the program with the given exit code.

    `ML` effect; its postcondition is `False`, so it does not return and the
    result type is arbitrary. *)
val exit : int -> ML 'a (ensures fun _ -> False)
(*| Runs the first function and, if it raises an exception, passes the exception to the handler.

    `try_with f h` returns the result of `f ()`, or of `h e` when `f ()` raises
    `e`. Both run in `ML` and nothing is specified about which branch is taken.

    ```fstar
    let safe_div (x y: int) : FStar.All.ML int =
      FStar.All.try_with
        (fun () -> if y = 0 then FStar.All.failwith "division by zero" else x / y)
        (fun _ -> 0)
    ``` *)
val try_with : (unit -> ML 'a) -> (exn -> ML 'a) -> ML 'a

exception Failure of string
(*| Raises the exception `Failure s`, aborting the current computation with the message `s`.

    `ML` effect; its postcondition is `False`, so it does not return normally
    and the result type is arbitrary. The exception `FStar.All.Failure` carries the
    message and can be caught with `FStar.All.try_with`. See also
    `FStar.Exn.raise` for raising any exception. *)
val failwith : s:string -> ML 'a (ensures fun _ -> False)
