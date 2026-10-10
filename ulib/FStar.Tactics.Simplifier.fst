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
module FStar.Tactics.Simplifier

open FStar.Tactics.V2
open FStar.Reflection.V2.Formula
open FStar.Reflection.Const

(* A correct-by-construction logical simplifier
 *
 * No calling `norm [simpl]`, that's cheating!
 *)

(*| Reflexivity of `<==>`: every proposition is equivalent to itself.

    Used by `FStar.Tactics.Simplifier.tiff` to close a goal `p <==> ?u` by
    unifying `?u` with `p`. *)
val lem_iff_refl : #a:prop -> Lemma (a <==> a)
let lem_iff_refl #a = ()

(*| Transitivity of `<==>`: from `a <==> b` and `b <==> c`, conclude `a <==> c`.

    Used by `FStar.Tactics.Simplifier.step` to split a simplification into two
    steps. *)
val lem_iff_trans : #a:prop -> #b:prop -> #c:prop -> squash (a <==> b) -> squash (b <==> c)
                                                            -> Lemma (a <==> c)
let lem_iff_trans #a #b #c _ _ = ()

(*| Solves the current goal `p <==> ?u` by instantiating `?u` with `p`, i.e. performs no simplification.

    Applies `FStar.Tactics.Simplifier.lem_iff_refl` with
    `FStar.Tactics.V2.Derived.apply_lemma`; fails if the goal cannot be unified
    with `p <==> p`. *)
let tiff () : Tac unit =
    apply_lemma (`lem_iff_refl)

(*| Splits the current goal `p <==> ?r` into `p <==> ?q` and `?q <==> ?r` for a fresh intermediate `?q`.

    Applies `FStar.Tactics.Simplifier.lem_iff_trans`; the two premises become
    the new goals, in that order. *)
let step () : Tac unit =
    apply_lemma (`lem_iff_trans)

(*| Simplification rule: `True /\ p` simplifies to `p`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_true_and_p : #p:prop -> Lemma ((True /\ p) <==> p)
let lem_true_and_p #p = ()

(*| Simplification rule: `p /\ True` simplifies to `p`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_p_and_true : #p:prop -> Lemma ((p /\ True) <==> p)
let lem_p_and_true #p = ()

(*| Simplification rule: `False /\ p` simplifies to `False`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_false_and_p : #p:prop -> Lemma ((False /\ p) <==> False)
let lem_false_and_p #p = ()

(*| Simplification rule: `p /\ False` simplifies to `False`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_p_and_false : #p:prop -> Lemma ((p /\ False) <==> False)
let lem_p_and_false #p = ()

(*| Simplification rule: `True \/ p` simplifies to `True`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_true_or_p : #p:prop -> Lemma ((True \/ p) <==> True)
let lem_true_or_p #p = ()

(*| Simplification rule: `p \/ True` simplifies to `True`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_p_or_true : #p:prop -> Lemma ((p \/ True) <==> True)
let lem_p_or_true #p = ()

(*| Simplification rule: `False \/ p` simplifies to `p`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_false_or_p : #p:prop -> Lemma ((False \/ p) <==> p)
let lem_false_or_p #p = ()

(*| Simplification rule: `p \/ False` simplifies to `p`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_p_or_false : #p:prop -> Lemma ((p \/ False) <==> p)
let lem_p_or_false #p = ()

(*| Simplification rule: `True ==> p` simplifies to `p`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_true_imp_p : #p:prop -> Lemma ((True ==> p) <==> p)
let lem_true_imp_p #p = ()

(*| Simplification rule: `p ==> True` simplifies to `True`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_p_imp_true : #p:prop -> Lemma ((p ==> True) <==> True)
let lem_p_imp_true #p = ()

(*| Simplification rule: `False ==> p` simplifies to `True`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_false_imp_p : #p:prop -> Lemma ((False ==> p) <==> True)
let lem_false_imp_p #p = ()

(*| Simplification rule: `forall (x:a). True` simplifies to `True`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_fa_true : #a:Type -> Lemma ((forall (x:a). True) <==> True)
let lem_fa_true #a = ()

(*| Simplification rule: `forall (x:a). False` simplifies to `False` when `a` is inhabited.

    The witness `x` is required because over an empty type the quantifier is
    true. `FStar.Tactics.Simplifier.simplify_point` supplies it with
    `FStar.Tactics.Simplifier.inhabit`. *)
val lem_fa_false : #a:Type -> (x:a) -> Lemma ((forall (x:a). False) <==> False)
let lem_fa_false #a x = ()

(*| Simplification rule: `exists (x:a). False` simplifies to `False`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_ex_false : #a:Type -> Lemma ((exists (x:a). False) <==> False)
let lem_ex_false #a = ()

(*| Simplification rule: `exists (x:a). True` simplifies to `True` when `a` is inhabited.

    The witness `x` is required because over an empty type the quantifier is
    false. `FStar.Tactics.Simplifier.simplify_point` supplies it with
    `FStar.Tactics.Simplifier.inhabit`. *)
val lem_ex_true : #a:Type -> (x:a) -> Lemma ((exists (x:a). True) <==> True)
let lem_ex_true #a x = ()

(*| Simplification rule: `~False` simplifies to `True`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_neg_false : unit -> Lemma (~False <==> True)
let lem_neg_false () = ()

(*| Simplification rule: `~True` simplifies to `False`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_neg_true : unit -> Lemma (~True <==> False)
let lem_neg_true () = ()

(*| Simplification rule: `True <==> p` simplifies to `p`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_true_iff_p : #p:prop -> Lemma ((True <==> p) <==> p)
let lem_true_iff_p #p = ()

(*| Simplification rule: `False <==> p` simplifies to `~p`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_false_iff_p : #p:prop -> Lemma ((False <==> p) <==> ~p)
let lem_false_iff_p #p = ()

(*| Simplification rule: `p <==> True` simplifies to `p`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_p_iff_true : #p:prop -> Lemma ((p <==> True) <==> p)
let lem_p_iff_true #p = ()

(*| Simplification rule: `p <==> False` simplifies to `~p`.

    Used by `FStar.Tactics.Simplifier.simplify_point`. *)
val lem_p_iff_false : #p:prop -> Lemma ((p <==> False) <==> ~p)
let lem_p_iff_false #p = ()

(*| Congruence of conjunction under `<==>`: from `p <==> p'` and `q <==> q'`, conclude `p /\ q <==> p' /\ q'`.

    Used by `FStar.Tactics.Simplifier.recurse` to simplify both operands;
    applying it leaves one goal per operand. *)
val and_cong (#p #q #p' #q' : prop) : squash (p <==> p') ->
                                      squash (q <==> q') ->
                                      Lemma ((p /\ q) <==> (p' /\ q'))
let and_cong #p #q #p' #q' _ _ = ()

(*| Congruence of disjunction under `<==>`: from `p <==> p'` and `q <==> q'`, conclude `p \/ q <==> p' \/ q'`.

    Used by `FStar.Tactics.Simplifier.recurse` to simplify both operands;
    applying it leaves one goal per operand. *)
val or_cong (#p #q #p' #q' : prop) : squash (p <==> p') ->
                                     squash (q <==> q') ->
                                     Lemma ((p \/ q) <==> (p' \/ q'))
let or_cong #p #q #p' #q' _ _ = ()

(*| Congruence of implication under `<==>`: from `p <==> p'` and `q <==> q'`, conclude `(p ==> q) <==> (p' ==> q')`.

    Used by `FStar.Tactics.Simplifier.recurse` to simplify both operands;
    applying it leaves one goal per operand. *)
val imp_cong (#p #q #p' #q' : prop) : squash (p <==> p') ->
                                      squash (q <==> q') ->
                                      Lemma ((p ==> q) <==> (p' ==> q'))
let imp_cong #p #q #p' #q' _ _ = ()

(*| Congruence of `forall` under `<==>`: if `p x <==> q x` for every `x`, then `forall x. p x` is equivalent to `forall x. q x`.

    Used by `FStar.Tactics.Simplifier.recurse` to simplify under a universal
    quantifier. *)
val fa_cong (#a : Type) (#p #q : a -> prop) :
    (x:a -> squash (p x <==> q x)) ->
    Lemma ((forall (x:a). p x) <==> (forall (x:a). q x))
let fa_cong #a #p #q f =
    introduce forall x. p x <==> q x with f x

(*| Congruence of `exists` under `<==>`: if `p x <==> q x` for every `x`, then `exists x. p x` is equivalent to `exists x. q x`.

    Used by `FStar.Tactics.Simplifier.recurse` to simplify under an existential
    quantifier. *)
val ex_cong (#a : Type) (#p #q : a -> prop) :
    (x:a -> squash (p x <==> q x)) ->
    Lemma ((exists (x:a). p x) <==> (exists (x:a). q x))
let ex_cong #a #p #q f =
    introduce forall x. p x <==> q x with f x

(*| Congruence of negation under `<==>`: `p <==> q` implies `~p <==> ~q`.

    Used by `FStar.Tactics.Simplifier.recurse` to simplify under a negation. *)
val neg_cong (#p #q:prop) : squash (p <==> q) -> Lemma (~p <==> ~q)
let neg_cong #p #q _ = ()

(*| Congruence of equivalence under `<==>`: from `p <==> p'` and `q <==> q'`, conclude `(p <==> q) <==> (p' <==> q')`.

    Used by `FStar.Tactics.Simplifier.recurse` to simplify both operands;
    applying it leaves one goal per operand. *)
val iff_cong (#p #p' #q #q' : prop) : squash (p <==> p') -> squash (q <==> q') -> Lemma ((p <==> q) <==> (p' <==> q'))
let iff_cong #p #p' #q #q' _ _ = ()

// Absolutely hideous, do something about normalization
(*| Checks syntactically whether a term is the formula `True`, also accepting a beta-redex whose function body is `True`.

    Uses `FStar.Reflection.V2.Formula.term_as_formula'`, so no normalization
    beyond that is performed. See `FStar.Tactics.Simplifier.is_false`. *)
val is_true : term -> Tac bool
let is_true t =
    begin match term_as_formula' t with
    | True_ -> true
    | _ -> begin match inspect t with
           | Tv_App l r ->
            begin match inspect l with
            | Tv_Abs b t ->
                begin match term_as_formula' t with
                | True_ -> true
                | _ -> false
                end
            | _ -> false
            end
           | _ -> false
           end
    end

(*| Checks syntactically whether a term is the formula `False`, also accepting a beta-redex whose function body is `False`.

    See `FStar.Tactics.Simplifier.is_true`. *)
val is_false : term -> Tac bool
let is_false t =
    begin match term_as_formula' t with
    | False_ -> true
    | _ -> begin match inspect t with
           | Tv_App l r ->
            begin match inspect l with
            | Tv_Abs b t ->
                begin match term_as_formula' t with
                | False_ -> true
                | _ -> false
                end
            | _ -> false
            end
           | _ -> false
           end
    end

(*| Solves a goal that is exactly the type `int`, `bool` or `unit` by providing a value of it (`42`, `true` or `()`).

    Fails on any other goal. Used to provide the witness needed by
    `FStar.Tactics.Simplifier.lem_fa_false` and
    `FStar.Tactics.Simplifier.lem_ex_true`, so those rules only fire on these
    three types. *)
val inhabit : unit -> Tac unit
let inhabit () =
    let t = cur_goal () in
    match inspect t with
    | Tv_FVar fv ->
        let qn = inspect_fv fv in
             if qn = int_lid  then exact (`42)
        else if qn = bool_lid then exact (`true)
        else if qn = unit_lid then exact (`())
        else fail ""
    | _ -> fail ""

(*| Simplifies the formula `p` of a goal `p <==> ?u`, solving the goal and instantiating `?u` with the simplified formula.

    It first simplifies the subformulas with `FStar.Tactics.Simplifier.recurse`,
    then applies one top-level rule such as
    `FStar.Tactics.Simplifier.lem_true_and_p`, or
    `FStar.Tactics.Simplifier.tiff` if none applies. Fails if the goal is not an
    `<==>`. *)
val simplify_point : unit -> Tac unit
(*| Simplifies the immediate subformulas of `p` in a goal `p <==> ?u` and leaves the goal for the rebuilt formula.

    Uses `FStar.Tactics.Simplifier.step` and the congruence lemmas such as
    `FStar.Tactics.Simplifier.and_cong`, calling
    `FStar.Tactics.Simplifier.simplify_point` on each operand. Mutually recursive
    with `FStar.Tactics.Simplifier.simplify_point`; fails if the goal is not an
    `<==>`. *)
val recurse : unit -> Tac unit

let rec simplify_point () =
    recurse ();
    norm [];
    let g = cur_goal () in
    let f = term_as_formula g in
    match f with
    | Iff l r ->
        begin match term_as_formula' l with
        | And p q ->
                 if is_true p  then apply_lemma (`lem_true_and_p)
            else if is_true q  then apply_lemma (`lem_p_and_true)
            else if is_false p then apply_lemma (`lem_false_and_p)
            else if is_false q then apply_lemma (`lem_p_and_false)
            else tiff ()

        | Or p q ->
                 if is_true p  then apply_lemma (`lem_true_or_p)
            else if is_true q  then apply_lemma (`lem_p_or_true)
            else if is_false p then apply_lemma (`lem_false_or_p)
            else if is_false q then apply_lemma (`lem_p_or_false)
            else tiff ()

        | Implies p q ->
                 if is_true p  then apply_lemma (`lem_true_imp_p)
            else if is_true q  then apply_lemma (`lem_p_imp_true)
            else if is_false p then apply_lemma (`lem_false_imp_p)
            else tiff ()

        | Forall _b _sort p ->
                 if is_true p  then apply_lemma (`lem_fa_true)
            else if is_false p then or_else (fun () -> apply_lemma (`lem_fa_false); inhabit ()) tiff
            else tiff ()

        | Exists _b _sort p ->
                 if is_false p then apply_lemma (`lem_ex_false)
            else if is_true  p then or_else (fun () -> apply_lemma (`lem_ex_true); inhabit ()) tiff
            else tiff ()

        | Not p ->
                 if is_true p  then apply_lemma (`lem_neg_true)
            else if is_false p then apply_lemma (`lem_neg_false)
            else tiff ()

        | Iff p q ->
            // After applying the lemma, we might still have more simpl to do,
            // so add an intermediate step.
            step ();
                 if is_true p  then apply_lemma (`lem_true_iff_p)
            else if is_true q  then apply_lemma (`lem_p_iff_true)
            else if is_false p then apply_lemma (`lem_false_iff_p)
            else if is_false q then apply_lemma (`lem_p_iff_false)
            else tiff ();
            simplify_point ()

        | _ -> tiff ()
        end
    | _ -> fail "simplify_point: failed precondition: goal should be `g <==> ?u`"

and recurse () : Tac unit =
    step ();
    norm [];
    let g = cur_goal () in
    let f = term_as_formula g in
    match f with
    | Iff l r ->
        begin match term_as_formula' l with
        | And _ _ ->
            seq (fun () -> apply_lemma (`and_cong)) simplify_point

        | Or _ _ ->
            seq (fun () -> apply_lemma (`or_cong)) simplify_point

        | Implies _ _ ->
            seq (fun () -> apply_lemma (`imp_cong)) simplify_point

        | Forall _ _ _ ->
            apply_lemma (`fa_cong);
            let _ = intro () in
            simplify_point ()

        | Exists _ _ _ ->
            apply_lemma (`ex_cong);
            let _ = intro () in
            simplify_point ()

        | Not _ ->
            apply_lemma (`neg_cong);
            simplify_point ()

        | Iff _ _ ->
            seq (fun () -> apply_lemma (`iff_cong)) simplify_point

        | _ -> tiff ()
        end
    | _ -> fail "recurse: failed precondition: goal should be `g <==> ?u`"

(*| Proves `p` from `p <==> q` and `q`.

    Used by `FStar.Tactics.Simplifier.simplify` to replace a goal by an
    equivalent one. *)
val equiv : #p:prop -> #q:prop -> squash (p <==> q) -> squash q -> Lemma p
let equiv #p #q _ _ = ()

(*| Replaces the current goal `p` by a logically equivalent, simplified goal `q`, proving the equivalence by construction.

    The rules remove `True` and `False` from conjunctions, disjunctions,
    implications, negations, equivalences and quantifiers, recursively.
    It does not call `norm [simpl]`; each step is justified by a lemma of this
    module. The simplified goal remains as the new goal.

    ```fstar
    let simplify_example (p:prop) =
      assert (True /\ (p \/ False) ==> p)
        by (FStar.Tactics.Simplifier.simplify ();
            let _ = FStar.Tactics.V2.implies_intro () in
            FStar.Tactics.V2.smt ())
    ``` *)
let simplify () : Tac unit =
    apply_lemma (`equiv);
    simplify_point ()
