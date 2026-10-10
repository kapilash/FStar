module FStar.Tactics.V2.SyntaxHelpers

open FStar.Reflection.V2
open FStar.Tactics.Effect
open FStar.Tactics.NamedView

(* These are fully-named variants of functions found in FStar.Reflection *)

(*| Splits a curried arrow type into its named binders and final computation
    type.

    Each arrow is opened with `FStar.Tactics.NamedView.inspect`, so the
    binders have fresh names and later sorts and the computation type refer to
    them as named variables. Collection stops at the first computation type
    whose effect is not `Tot`, which is returned. A type that is not an arrow
    gives no binders and `Tot` of the type. The named-view counterpart of
    `FStar.Reflection.V2.Collect.collect_arr_ln_bs`. *)
[@@plugin]
val collect_arr_bs : typ -> Tac (list binder & comp)

(*| Like `FStar.Tactics.V2.SyntaxHelpers.collect_arr_bs`, but returns only the
    sorts of the binders. *)
[@@plugin]
val collect_arr : typ -> Tac (list typ & comp)

(*| Splits nested abstractions into their named binders, in order, and the
    body.

    Each abstraction is opened with `FStar.Tactics.NamedView.inspect`, so the
    body refers to the binders as named variables. Ascriptions are not looked
    through. The named-view counterpart of
    `FStar.Reflection.V2.Collect.collect_abs_ln`. *)
[@@plugin]
val collect_abs : term -> Tac (list binder & term)

(*| Builds the curried arrow type `b1 -> ... -> bn -> cod` from named binders
    and a final computation type.

    Intermediate arrows have `Tot` computation types, and each binder is closed
    over the rest of the type by `FStar.Tactics.NamedView.pack`. Fails the
    tactic with `mk_arr, empty binders` if the list is empty. *)
[@@plugin]
val mk_arr (bs: list binder) (cod : comp) : Tac term

(*| Builds the curried arrow type `b1 -> ... -> bn -> Tot cod` from named
    binders, or `cod` when there are none.

    Each binder is closed over the rest of the type by
    `FStar.Tactics.NamedView.pack`. The named-view counterpart of
    `FStar.Reflection.V2.Derived.mk_tot_arr_ln`. *)
[@@plugin]
val mk_tot_arr (bs: list binder) (cod : term) : Tac term

(*| Finds the let binding for the name `nm` in a group of let bindings, as
    returned in `Sg_Let` by `FStar.Tactics.NamedView.inspect_sigelt`.

    Fails the tactic if no binding defines `nm`. *)
[@@plugin]
val lookup_lb (lbs:list letbinding) (nm:name) : Tac letbinding

(*| Inspects a term with `FStar.Tactics.NamedView.inspect`, looking through any
    number of type and computation-type ascriptions.

    The result is never `Tv_AscribedT` or `Tv_AscribedC`. The named-view
    counterpart of `FStar.Reflection.V2.Collect.inspect_ln_unascribe`. *)
[@@plugin]
val inspect_unascribe (t:term) : Tac (tv:term_view{notAscription tv})

(* Helpers for dealing with nested applications and arrows *)

(*| Splits a nested application `f a1 ... an` into its head `f` and the
    arguments `[a1; ...; an]` with their qualifiers.

    The term is inspected with `FStar.Tactics.V2.SyntaxHelpers.inspect_unascribe`
    at each step, so ascriptions are looked through. A term that is not an
    application gives itself and the empty list. The tactic counterpart of
    `FStar.Reflection.V2.Collect.collect_app_ln`.

    ```fstar
    let _ = assert True by (
      let hd, args = collect_app (`(1 + 2)) in
      guard (List.Tot.length args = 2);
      guard (is_fvar hd (implode_qn add_qn)))
    ``` *)
[@@plugin]
val collect_app (t:term) : Tac (term & list argv)

(*| Splits an application of a top-level name into the name, its universe
    instantiation and the arguments.

    Returns `None` if the head, as computed by
    `FStar.Tactics.V2.SyntaxHelpers.collect_app`, is not a top-level name. The
    universe list is empty when the name is not universe-instantiated. *)
[@@plugin]
val hua (t:term) : Tac (option (fv & universes & list argv))
