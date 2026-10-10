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
module FStar.Tactics.V2.Logic

open FStar.Tactics.Effect
open FStar.Reflection.V2
open FStar.Reflection.V2.Formula
open FStar.Tactics.NamedView
open FStar.Tactics.Logic.Lemmas {} (* bring lemmas into TC scope *)

(* Repeated to avoid importing FStar.Tactics.Derived. *)
private let cur_goal () : Tac typ =
  let open FStar.Stubs.Tactics.Types in
  let open FStar.Stubs.Tactics.V2.Builtins in
  match goals_of (get ()) with
  | g::_ -> goal_type g
  | _ -> raise (TacticFailure (mkmsg "no more goals", None))

(*| Returns the first goal viewed as a logical formula
    (`FStar.Reflection.V2.Formula.formula`), for matching on its shape
    (`And`, `Forall`, `Implies`, ...); fails if there are no goals. *)
let cur_formula () : Tac formula = term_as_formula (cur_goal ())

(*| Reverts the most recently introduced binder `x` of the first goal into a
    universal quantifier: the goal `p x` becomes `forall x. p x`.

    The inverse of `FStar.Tactics.V2.Logic.forall_intro`. *)
[@@plugin]
val l_revert () : Tac unit

(*| Applies `FStar.Tactics.V2.Logic.l_revert` once per element of the list,
    turning that many of the most recent binders back into universal
    quantifiers.

    Only the length of the list is used, not the bindings it contains. *)
[@@plugin]
val l_revert_all (bs:list binding) : Tac unit

(*| Introduces a universal quantifier: turns a goal `forall x. p x` into
    `p x` with a fresh `x` in the context, and returns the binding for `x`.

    Fails if the goal is not a `forall`. See also
    `FStar.Tactics.V2.Logic.forall_intros` and
    `FStar.Tactics.V2.Logic.l_intro`.

    ```fstar
    let _ = assert (forall (x:int). x > 0 ==> x >= 0)
              by (let _ = forall_intro () in
                  let _ = implies_intro () in
                  smt ())
    ``` *)
[@@plugin]
val forall_intro () : Tac binding

(*| Like `FStar.Tactics.V2.Logic.forall_intro`, but gives the introduced
    variable the given name. *)
[@@plugin]
val forall_intro_as (s:string) : Tac binding

(*| Introduces consecutive universal quantifiers of the goal, returning the
    new bindings; fails if the goal does not start with a `forall`. *)
[@@plugin]
val forall_intros () : Tac (list binding)

(*| Splits a conjunction goal `p /\ q` into two goals, `p` then `q`; fails
    with "Could not split goal" otherwise.

    ```fstar
    let _ = assert (True /\ 1 + 1 == 2) by (split (); trivial (); trivial ())
    ``` *)
[@@plugin]
val split () : Tac unit

(*| Introduces an implication: turns a goal `p ==> q` into `q` with a
    hypothesis of type `squash p` in the context, and returns that
    hypothesis.

    Fails if the goal is not an implication. See also
    `FStar.Tactics.V2.Logic.implies_intros` and
    `FStar.Tactics.V2.Logic.l_intro`. *)
[@@plugin]
val implies_intro () : Tac binding

(*| Like `FStar.Tactics.V2.Logic.implies_intro`, but gives the hypothesis
    the given name. *)
[@@plugin]
val implies_intro_as (s:string) : Tac binding

(*| Introduces consecutive implications of the goal as hypotheses,
    returning them; fails if the goal is not an implication. *)
[@@plugin]
val implies_intros () : Tac (list binding)

(*| Introduces a universal quantifier or an implication, whichever the goal
    starts with, and returns the new binding; fails if it is neither.

    The logical counterpart of `FStar.Stubs.Tactics.V2.Builtins.intro`,
    which works on arrows. *)
[@@plugin]
val l_intro () : Tac binding

(*| Introduces all leading universal quantifiers and implications of the
    goal, returning the new bindings; never fails (it may introduce
    nothing). *)
[@@plugin]
val l_intros () : Tac (list binding)

(*| Solves the first goal with the given proof term; the same as
    `FStar.Tactics.V2.Derived.exact`. *)
[@@plugin]
val l_exact (t:term) : Tac unit

// FIXME: should this take a binding? It's less general...
// but usually what we want. Coercions could help.
(*| Solves the first goal with the given variable, typically a hypothesis
    whose type is the goal.

    See also `FStar.Tactics.V2.Derived.assumption`, which searches the
    context. *)
[@@plugin]
val hyp (x:namedv) : Tac unit

(*| Adds the postcondition of a lemma application to the context of the
    first goal as a new hypothesis, and returns it.

    The term is applied (with `FStar.Tactics.V2.Derived.pose_apply`), so a
    precondition of the lemma that is not discharged automatically becomes a
    new goal, placed after the existing goals. *)
[@@plugin]
val pose_lemma (t : term) : Tac binding

(*| Repeatedly introduces quantifiers and implications and splits
    conjunctions, on the first goal and all goals this produces; never
    fails. *)
[@@plugin]
val explode () : Tac unit

(*| For a goal `x == e ==> p`, introduces the equation, substitutes `e` for
    `x` in `p` and drops the equation, then does the same for equality
    implications nested under quantifiers, conjunctions and implications.

    Fails with "Not an equality implication" if the goal does not have this
    shape. See also `FStar.Tactics.V2.Logic.rewrite_all_equalities`. *)
[@@plugin]
val simplify_eq_implication () : Tac unit

(*| Substitutes away the equality hypotheses of every equality implication
    `x == e ==> p` in the goal, looking under universal quantifiers,
    conjunctions and implications.

    Built on `FStar.Tactics.V2.Logic.simplify_eq_implication`. *)
[@@plugin]
val rewrite_all_equalities () : Tac unit

(*| Proves a goal that is an application of the given predicate by
    `FStar.Tactics.V2.Derived.trivial`, after substituting away leading
    equality implications `x == e ==> ...` and descending under
    quantifiers, conjunctions and implications.

    Fails with "Not an equality implication" when a goal is neither an
    application nor an equality implication. An application of another head
    is left unchanged. *)
[@@plugin]
val unfold_definition_and_simplify_eq (tm:term) : Tac unit

(*| Case analysis on a disjunction: given a proof of `p \/ q`, replaces a
    goal `phi` by the two goals `p ==> phi` and `q ==> phi`. *)
[@@plugin]
val cases_or (o:term) : Tac unit

(*| Case analysis on a boolean term `b`: replaces the first goal by one goal
    where `b` is `true` and one where it is `false`, with `b` rewritten in
    each goal when it is a variable. *)
[@@plugin]
val cases_bool (b:term) : Tac unit

(*| Proves a disjunction `p \/ q` by proving its left side: the goal
    becomes `p`.

    See `FStar.Tactics.V2.Logic.right`. *)
[@@plugin]
val left () : Tac unit

(*| Proves a disjunction `p \/ q` by proving its right side: the goal
    becomes `q`.

    ```fstar
    let _ = assert (False \/ True) by (right (); trivial ())
    ``` *)
[@@plugin]
val right () : Tac unit

(*| Uses a proof of a conjunction `p /\ q`: turns the goal `phi` into
    `p ==> q ==> phi`.

    See `FStar.Tactics.V2.Logic.destruct_and`, which also introduces both
    hypotheses. *)
[@@plugin]
val and_elim (t : term) : Tac unit

(*| Uses a proof of a conjunction `p /\ q`, adding hypotheses for `p` and
    for `q` to the context of the first goal, and returns them. *)
[@@plugin]
val destruct_and (t : term) : Tac (binding & binding)

(*| Proves an existential goal `exists x. p x` with the given witness `t`:
    the goal becomes `p t`.

    ```fstar
    let _ = assert (exists (n:nat). n > 2) by (witness (`3))
    ``` *)
[@@plugin]
val witness (t : term) : Tac unit

(*| Uses a proof of an existential `exists x. p x`: adds a variable `x` and
    a hypothesis `p x` to the context of the first goal, and returns both
    (the witness, then the proof). *)
[@@plugin]
val elim_exists (t : term) : Tac (binding & binding)

(*| Instantiates a proof of a universal statement `forall x. p x` at the
    given term `t`, adding `p t` as a new hypothesis, and returns it; fails
    with "could not instantiate" if that does not typecheck.

    See also `FStar.Tactics.V2.Logic.instantiate_as`. *)
[@@plugin]
val instantiate (fa : term) (x : term) : Tac binding

(*| Like `FStar.Tactics.V2.Logic.instantiate`, but gives the new hypothesis
    the given name. *)
[@@plugin]
val instantiate_as (fa : term) (x : term) (s : string) : Tac binding

(*| Eliminates the existentials in the hypotheses of the first goal: for
    each binding of the context that is an existential, introduces
    variables for its witnesses and a hypothesis for its body.

    Returns, for each binding of the context, the list of introduced
    witnesses and the resulting hypothesis (the binding itself if it was not
    an existential). *)
[@@plugin]
val skolem () : Tac (list (list binding & binding))

(*| Adds a lemma to the context of the first goal as a hypothesis quantified
    over its arguments, `forall x. pre x ==> post x`, and returns it.

    Only lemmas with one to three arguments are supported, and the term is
    expected to be a top-level name. Fails otherwise, with
    `using_lemma: failed to instantiate`. *)
[@@plugin]
val using_lemma (t : term) : Tac binding
