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
module FStar.Reflection.V2.Collect

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

(*| Inspects a term with `FStar.Stubs.Reflection.V2.Builtins.inspect_ln`,
    looking through any number of type and computation-type ascriptions.

    The returned view is never `Tv_AscribedT` or `Tv_AscribedC`, and it
    precedes the original term, so recursive functions can use it for
    termination. `FStar.Reflection.V2.Derived.inspect_ln_unascribe` is an
    identical copy; `FStar.Tactics.V2.SyntaxHelpers.inspect_unascribe` is the
    named-view counterpart. *)
let rec inspect_ln_unascribe (t:term) : tv:term_view{tv << t /\ notAscription tv} =
    match inspect_ln t with
    | Tv_AscribedT t' _ _ _
    | Tv_AscribedC t' _ _ _ -> inspect_ln_unascribe t'
    | tv -> tv

// (* Helpers for dealing with nested applications and arrows *)
(*| Splits a nested application into its head and arguments, appending the
    accumulated arguments `args` after the collected ones.

    The worker of `FStar.Reflection.V2.Collect.collect_app_ln`, which starts
    with an empty accumulator. *)
let rec collect_app_ln' (args : list argv) (t : term) : Tot (term & list argv) (decreases t) =
    match inspect_ln_unascribe t with
    | Tv_App l r ->
        collect_app_ln' (r::args) l
    | _ -> (t, args)

(*| Splits a nested application `f a1 ... an` into its head `f` and the
    arguments `[a1; ...; an]` with their qualifiers.

    Works on the locally nameless syntax, without opening binders, and looks
    through ascriptions on the head. A term that is not an application gives
    itself and the empty list.
    `FStar.Reflection.V2.Derived.Lemmas.collect_app_ref` additionally proves
    that the results precede the term; `FStar.Tactics.V2.SyntaxHelpers.collect_app`
    is the named-view counterpart. `FStar.Reflection.V2.Derived.mk_app` is the
    inverse. *)
val collect_app_ln : term -> term & list argv
let collect_app_ln = collect_app_ln' []

(*| Collects the binders of a curried arrow from a computation type, pushing
    them in reverse order onto the accumulator `bs`.

    It descends into the result type of `c` only while `c` is a `Tot`
    computation whose result, after ascriptions, is an arrow. The worker of
    `FStar.Reflection.V2.Collect.collect_arr_ln_bs`. *)
let rec collect_arr' (bs : list binder) (c : comp) : Tot (list binder & comp) (decreases c) =
    let cv = inspect_comp c in
    if is_tot_comp cv then
      begin match inspect_ln_unascribe cv.result_typ with
      | Tv_Arrow b c ->
          collect_arr' (b::bs) c
      | _ ->
          (bs, c)
      end
    else (bs, c)

(*| Splits a curried arrow type into its binders and final computation type.

    For `x1:t1 -> ... -> xn:tn -> C` it returns the binders `x1` to `xn` in
    order and `C`. Collection stops at the first computation type whose effect
    is not `Tot` (for instance `GTot` or an effectful arrow), which is then
    returned as `C`. A type that is not an arrow gives no binders and
    the computation `Tot t`. The binders are not opened: later sorts and `C`
    refer to earlier binders by de Bruijn index. See
    `FStar.Tactics.V2.SyntaxHelpers.collect_arr_bs` for the named-view
    counterpart. *)
val collect_arr_ln_bs : typ -> list binder & comp
let collect_arr_ln_bs t =
    let (bs, c) = collect_arr' [] (pack_comp (mk_tot_comp t)) in
    (List.Tot.Base.rev bs, c)

(*| Like `FStar.Reflection.V2.Collect.collect_arr_ln_bs`, but returns only the
    sorts of the binders. *)
val collect_arr_ln : typ -> list typ & comp
let collect_arr_ln t =
    let bs, c = collect_arr_ln_bs t in
    List.Tot.Base.map (fun b -> (inspect_binder b).sort) bs, c

(*| Collects the binders of nested abstractions, pushing them in reverse order
    onto the accumulator `bs`; the worker of
    `FStar.Reflection.V2.Collect.collect_abs_ln`. *)
let rec collect_abs' (bs : list binder) (t : term) : Tot (list binder & term) (decreases t) =
    match inspect_ln_unascribe t with
    | Tv_Abs b t' ->
        collect_abs' (b::bs) t'
    | _ -> (bs, t)

(*| Splits nested abstractions `fun x1 ... xn -> body` into the binders, in
    order, and the body.

    Looks through ascriptions. The binders are not opened, so the body refers to
    them by de Bruijn index. A term that is not an abstraction gives no binders
    and itself. See `FStar.Tactics.V2.SyntaxHelpers.collect_abs` for the
    named-view counterpart. *)
val collect_abs_ln : term -> list binder & term
let collect_abs_ln t =
    let (bs, t') = collect_abs' [] t in
    (List.Tot.Base.rev bs, t')