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
module FStar.Tactics.Effect

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Tactics.Types

(* This module is extracted, don't add any `assume val`s or extraction
 * will break. (`synth_by_tactic` is fine) *)

(*| The representation of a tactic: a possibly divergent function from a reference to the proof state to a result.

    It plays no role in typechecking and is only used for extraction and reification of the `TAC` effect, whose return and bind are `FStar.Tactics.Effect.tac_return` and `FStar.Tactics.Effect.tac_bind`. *)
inline_for_extraction
let tac_repr (a:Type) : Type = ref_proofstate -> Dv a

(*| The return of the `TAC` effect: the tactic that ignores the proof state and returns `x`. *)
inline_for_extraction
let tac_return (a:Type) (x:a) : tac_repr a =
  fun _ -> x

(*| The bind of the `TAC` effect: runs `t1` on the proof state, then runs `t2` applied to its result on the same proof state. *)
inline_for_extraction
let tac_bind (a:Type) (b:Type) (t1:tac_repr a) (t2:(a -> tac_repr b)) : tac_repr b =
  fun ps ->
  let x = t1 ps in
  t2 x ps

/// default effect is Tac : meaning, unannotated TAC functions will be
///                         typed as Tac a

[@@ default_effect "FStar.Tactics.Effect.Tac"]
reflectable
effect { TAC with { repr = tac_repr; return = tac_return; bind = tac_bind } }

(* Hoare variant *)
effect TacH (a:Type) = TAC a

(* "Total" variant *)
effect Tac (a:Type) = TAC a

(* Metaprograms that succeed *)
effect TacS (a:Type) = TAC a

(* Always succeed, no effect *)
effect TacRO (a:Type) = TAC a

(* A variant that doesn't prove totality (nor type safety!).

   A precondition is an obligation on the *caller* now, and an effect
   abbreviation has no arrow of its own to hang one on, so [TacF] can no longer
   hand [False] to the body of a metaprogram.  Take the falsity as an argument
   instead -- see [assume_safe] below, whose argument type is
   [squash False -> Tac a]. *)
effect TacF (a:Type) = TAC a

(*| A technical marker opening the region of the interface in which the lifts into `TAC` are defined; it is not meant to be used.

    The implementation typechecks that region with SMT queries admitted. Closed by `FStar.Tactics.Effect.lift_div_tac_interleave_end`. *)
val lift_div_tac_interleave_begin : unit
#push-options "--admit_smt_queries true"
(*| The lift from `Div` to `TAC`, which lets divergent code run inside tactics: the resulting tactic ignores the proof state and runs `f`.

    Used by `sub_effect Div ~> TAC`. *)
inline_for_extraction
let lift_div_tac (a:Type) (f:unit -> Dv a) : tac_repr a
  = fun _ -> f ()
(*| The lift from `NDET` to `TAC`: the resulting tactic ignores the proof state and runs `f`.

    `NDET` already reaches `TAC` through `DIV`, but this direct lift spares reification (hence extraction of metaprograms) from going through the representation of `DIV`, which does not exist. Used by `sub_effect NDET ~> TAC`. *)
inline_for_extraction
let lift_ndet_tac (a:Type) (f:unit -> Nd a) : tac_repr a
  = fun _ -> f ()
#pop-options
(*| A technical marker closing the region opened by `FStar.Tactics.Effect.lift_div_tac_interleave_begin`; it is not meant to be used. *)
val lift_div_tac_interleave_end : unit

sub_effect Div ~> TAC = lift_div_tac

(* [NDET] reaches [TAC] through [DIV] already, but we give the lift
   explicitly so that reification (hence extraction of metaprograms) does
   not have to go through [DIV]'s (nonexistent) representation. *)
sub_effect NDET ~> TAC = lift_ndet_tac

/// assert p by t

(*| Marks a proposition `p` to be proved by running the tactic `t` rather than by SMT.

    When a verification condition contains `with_tactic t p`, the engine runs `t` on a goal for `p` instead of sending `p` to SMT; goals that remain after the tactic are sent to the SMT solver. Logically the marker is equivalent to `p` (see `FStar.Tactics.Effect.by_tactic_seman` and `FStar.Tactics.Effect.unfold_with_tactic`). It is usually introduced by `assert p by t` through `FStar.Tactics.Effect.assert_by_tactic`. *)
val with_tactic (t : unit -> Tac unit) (p:prop) : prop

(*| Marks a term to be rewritten by a tactic: `rewrite_with_tactic t x` is replaced by a term that the tactic proves equal to `x`.

    When the marker is met, the engine creates a goal `x == ?u` for a new unification variable `?u` and runs `t` on it. If afterwards `?u` is solved and only trivial goals remain, the marker is replaced by the solution of `?u`. Logically, `rewrite_with_tactic t x` equals `x` (see `FStar.Tactics.Effect.unfold_rewrite_with_tactic`). *)
val rewrite_with_tactic (t:unit -> Tac unit) (#a:Type) (x:a) : a

(*| Synthesizes a term of type `t` by running a tactic whose single goal is `t`; the meaning of the syntax `_ by tau`.

    The type looks unsound, but it should not lead to inconsistency: wherever this term appears during typechecking it must be fully applied, and the tactic is run. A failure of the tactic is a typechecking failure. Think of it as a language construct rather than a real function.

    ```fstar
    let forty_two : int = _ by (exact (`42))
    ``` *)
val synth_by_tactic : (#t:Type) -> (unit -> Tac unit) -> Tot t

(*| Proves `p` by running a tactic on it rather than by SMT; the meaning of the syntax `assert p by tau`.

    Its precondition is `FStar.Tactics.Effect.with_tactic t p`, which makes the engine run `t` on a goal for `p`. Goals that remain after the tactic are sent to the SMT solver.

    ```fstar
    let _ = assert (True /\ True) by (split (); trivial (); trivial ())
    ``` *)
val assert_by_tactic (p:prop) (t:unit -> Tac unit)
  : Pure unit
         (requires (set_range_of (with_tactic t p) (range_of t)))
         (ensures (fun _ -> p))

(*| States that `FStar.Tactics.Effect.with_tactic tau phi` implies `phi`: the tactic marker does not change the meaning of the proposition. *)
val by_tactic_seman (tau:unit -> Tac unit) (phi:prop)
  : Lemma (with_tactic tau phi ==> phi)

(*| Runs a metaprogram without proving that it is well-formed, by letting it assume `False`.

    This is fine since metaprograms only run at typechecking time; if one gets stuck, the compiler simply raises an error. The argument's binder has type `squash False` rather than `unit`: that is how the metaprogram assumes it is unreachable and may be partial. Write `assume_safe (fun _ -> ...)`, not `fun () -> ...`: a unit pattern forces the binder's type to `unit` and so loses the `False`. *)
let assume_safe (#a:Type) (tau:squash False -> Tac a) : Tac a = admit (); tau ()

private let tac a b = a -> Tac b
private let tactic a = tac unit a

(*| An attribute that runs a tactic on the definition of a top-level `let` before it is typechecked and elaborated.

    The tactic `tau` receives a quotation of the definition (once for each definition if there are several) and its result replaces the definition. No goals are involved and there is no proof obligation. Use it as `[@@preprocess_with tau]`. *)
val preprocess_with (tau : term -> Tac term) : Tot unit

(*| An attribute that rewrites a definition, after typechecking, into a provably equal shape chosen by a tactic.

    On `let x = E`, the metaprogram is given a goal `E == ?u` for a fresh `?u`, and must both instantiate `?u` and prove the equality. Useful for custom transformations before extraction, such as selective inlining. See `FStar.Tactics.Effect.postprocess_for_extraction_with` for a version that only affects extraction, and `FStar.Tactics.Effect.postprocess_type` to process the type too.

    ```fstar
    [@@postprocess_with (fun () -> norm [delta_only [`%forty_two]]; trefl ())]
    let fifty : int = forty_two + 8
    ``` *)
val postprocess_with (tau : unit -> Tac unit) : Tot unit

(*| Like `FStar.Tactics.Effect.postprocess_with`, but the metaprogram only runs before extraction, so typechecking and the logical environment are not affected at all. *)
val postprocess_for_extraction_with (tau : unit -> Tac unit) : Tot unit

(*| An attribute which, together with `FStar.Tactics.Effect.postprocess_with` or `FStar.Tactics.Effect.postprocess_for_extraction_with`, says that the type of the definition should be processed by the same tactic too. *)
val postprocess_type : unit

#set-options "--no_tactics"

(*| Proves `FStar.Tactics.Effect.with_tactic t p` from `p`, without running the tactic: the converse of `FStar.Tactics.Effect.by_tactic_seman`.

    Checked with tactics disabled, so the marker is treated as an ordinary proposition here. *)
val unfold_with_tactic (t:unit -> Tac unit) (p:prop)
  : Lemma (requires p)
          (ensures (with_tactic t p))

(*| States that `FStar.Tactics.Effect.rewrite_with_tactic t p` is equal to `p`.

    Checked with tactics disabled, so the marker is treated as an ordinary term here. *)
val unfold_rewrite_with_tactic (t:unit -> Tac unit) (#a:Type) (p:a)
  : Lemma (rewrite_with_tactic t p == p)
