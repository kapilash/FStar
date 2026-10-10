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
module FStar.Option

open FStar.All

(*| Returns `true` exactly when the option is `None`. *)
inline_for_extraction
val isNone: option 'a -> Tot bool
inline_for_extraction
let isNone = function
  | None -> true
  | Some _ -> false

(*| Returns `true` exactly when the option is `Some v` for some `v`. *)
inline_for_extraction
val isSome: option 'a -> Tot bool
inline_for_extraction
let isSome = function
  | Some _ -> true
  | None -> false

(*| Applies `f` to the value inside `Some`, and leaves `None` unchanged.

    `f` may have effects in `ML`, so the whole call is `ML`. For a total
    function, use `FStar.Option.mapTot`, which can be used in
    specifications. *)
inline_for_extraction
val map: ('a -> ML 'b) -> option 'a -> ML (option 'b)
inline_for_extraction
let map f = function
  | Some x -> Some (f x)
  | None -> None

(*| Applies the total function `f` to the value inside `Some`, and
    leaves `None` unchanged.

    The total counterpart of `FStar.Option.map`. *)
inline_for_extraction
val mapTot: ('a -> Tot 'b) -> option 'a -> Tot (option 'b)
inline_for_extraction
let mapTot f = function
  | Some x -> Some (f x)
  | None -> None

(*| Returns the value inside `Some`.

    Raises an exception, by `failwith`, when the option is `None`; that is
    why it is in `ML`. In specifications and total code, match on the
    option or use `FStar.Pervasives.Native.Some?.v` with a `Some?`
    precondition instead. *)
inline_for_extraction
val get: option 'a -> ML 'a
let get = function
  | Some x -> x
  | None -> failwith "empty option"

(*| Monadic bind for options, written `let? x = e1 in e2`.

    If `e1` is `Some v`, continues with `e2` where `x` is `v`; if it is
    `None`, the whole expression is `None`. *)
let (let?) (x: option 'a) (f: 'a -> option 'b): option 'b
  = match x with
  | Some x -> f x
  | None   -> None

(*| Pairs two options, for `let? x = e1 and? y = e2 in e`.

    Returns `Some (x, y)` when both are `Some`, and `None` otherwise. *)
let (and?) (x: option 'a) (y: option 'b): option ('a & 'b)
  = match x, y with
  | Some x, Some y -> Some (x, y)
  | _ -> None
