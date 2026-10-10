module FStar.Tactics.MApply

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Tactics.Effect
open FStar.Tactics.V2.SyntaxCoercions

include FStar.Tactics.MApply0

(*| Typeclass of values that can be converted to a term with `to_term`, so that `FStar.Tactics.MApply.mapply` accepts both terms and bindings.

    Instances: `FStar.Tactics.MApply.termable_term` and
    `FStar.Tactics.MApply.termable_binding`. *)
class termable (a : Type) = {
  to_term : a -> Tac term
}

(*| `FStar.Tactics.MApply.termable` instance for terms: the identity. *)
instance termable_term : termable term = {
  to_term = (fun t -> t);
}

(*| `FStar.Tactics.MApply.termable` instance for bindings (hypotheses), which converts a binding to the variable it binds. *)
instance termable_binding : termable binding = {
  to_term = (fun b -> binding_to_term b);
}

(*| Applies a lemma, function or hypothesis to solve the current goal, trying harder than `FStar.Tactics.V2.Derived.apply` and `FStar.Tactics.V2.Derived.apply_lemma`.

    The argument can be a term or a binding (see
    `FStar.Tactics.MApply.termable`). It runs
    `FStar.Tactics.MApply0.mapply0` on the corresponding term: it tries
    `apply`, then `apply_lemma`, and if the conclusion is an implication
    `p ==> q` it reduces the goal to `p` and the implication, so lemmas of the
    form `Lemma (p ==> q)` can be used backwards. Remaining premises become
    new goals.

    ```fstar
    let mapply_example (p q:prop) (lem:unit -> Lemma (p ==> q)) (hp:squash p) : squash q =
      _ by (FStar.Tactics.MApply.mapply (quote lem);
            FStar.Tactics.MApply.mapply (quote hp))
    ``` *)
let mapply (#ty:Type) {| termable ty |} (x : ty) : Tac unit =
  let t = to_term x in
  mapply0 t
