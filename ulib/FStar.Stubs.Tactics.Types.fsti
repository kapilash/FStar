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
module FStar.Stubs.Tactics.Types

open FStar.Stubs.Reflection.Types
include FStar.Stubs.Tactics.Common

(*| A goal of a tactic: an environment, a type to inhabit (`FStar.Stubs.Tactics.Types.goal_type`) and a witness, the unification variable to be solved (`FStar.Stubs.Tactics.Types.goal_witness`).

    Abstract and implemented by the compiler. A goal also carries its options, a label and whether it comes from a guard. *)
assume new type goal
(*| The state of a running tactic, including its list of goals, its list of SMT goals and the environment in which it started.

    Abstract and implemented by the compiler. Obtain it with `FStar.Stubs.Tactics.V2.Builtins.get`. *)
assume new type proofstate

(*| The type of the mutable reference to the proof state that a tactic receives at run time.

    Used only in the representation of tactics, `FStar.Tactics.Effect.tac_repr`; tactic code never handles it directly. Implemented by the compiler. *)
val ref_proofstate : Type0

(*| Returns the active goals of a proof state, the first being the current goal.

    `FStar.Tactics.V2.Derived.goals` applies it to the current proof state. *)
val goals_of     : proofstate -> list goal
(*| Returns the goals of a proof state that have been set aside for the SMT solver.

    These are sent to SMT if they remain at the end of the tactic run. `FStar.Tactics.V2.Derived.smt_goals` applies it to the current proof state. *)
val smt_goals_of : proofstate -> list goal

(* Inspecting a goal *)
(*| Returns the environment (context) of a goal.

    `FStar.Tactics.V2.Derived.cur_env` returns that of the current goal. *)
val goal_env     : goal -> env
(*| Returns the type of a goal, the type that its witness must inhabit.

    For a proposition the type is usually `squash phi`. `FStar.Tactics.V2.Derived.cur_goal` returns that of the current goal. *)
val goal_type    : goal -> typ
(*| Returns the witness of a goal, the unification variable that solving the goal instantiates.

    `FStar.Tactics.V2.Derived.cur_witness` returns that of the current goal. *)
val goal_witness : goal -> term
(*| Returns whether the goal comes from a guard (a verification condition) rather than from the user's term. *)
val is_guard     : goal -> bool (* A bit of helper info: did this goal come from a VC guard? *)

(*| Returns the label of a goal, the empty string if it has none.

    A non-empty label is shown when the goal is printed and in the error reported when SMT cannot prove the goal. *)
val get_label    : goal -> string
(*| Returns the goal with its label replaced by the given string.

    This builds a new goal value; to affect the proof state, put it back with `FStar.Stubs.Tactics.V2.Builtins.set_goals`. *)
val set_label    : string -> goal -> goal

(* Tracing *)
(*| Returns the proof state with its tracing depth increased by one.

    The depth controls which tracepoints dump the proof state (see `FStar.Stubs.Tactics.Types.tracepoint`). Used by the tactic engine around calls. *)
val incr_depth : proofstate -> proofstate
(*| Returns the proof state with its tracing depth decreased by one, the inverse of `FStar.Stubs.Tactics.Types.incr_depth`. *)
val decr_depth : proofstate -> proofstate
(*| Dumps the proof state with the message "TRACE" when tactic tracing is enabled (`--tactic_trace`, or `--tactic_trace_d` at a large enough depth), and returns `true`.

    It always returns `true`; the result is a boolean rather than `unit` to prevent erasure. *)
val tracepoint : proofstate -> b:bool{b == true}
(*| Returns the proof state with the definition range of its entry range set to that of the given range.

    The entry range is the source location attached to the tactic run, used for instance in reports. *)
val set_proofstate_range : proofstate -> FStar.Range.range -> proofstate

(*| The order in which `FStar.Stubs.Tactics.V2.Builtins.ctrl_rewrite` traverses a term.

    - `TopDown`: preorder, a node before its subterms
    - `BottomUp`: postorder, the subterms before the node *)
type direction =
    | TopDown
    | BottomUp

(*| Tells `FStar.Stubs.Tactics.V2.Builtins.ctrl_rewrite` how to continue after visiting a subterm.

    - `Continue`: keep going with further subterms
    - `Skip`: do not descend into this subtree
    - `Abort`: stop the whole traversal *)
type ctrl_flag =
    | Continue
    | Skip
    | Abort

(*| What the tactic engine does with a guard (a verification condition) that arises internally, for instance while typechecking a term given to `FStar.Tactics.V2.Derived.exact`.

    - `Goal`: add it as an ordinary goal
    - `SMT`: add it as an SMT goal
    - `SMTSync`: send it to SMT immediately, logging (not raising) errors if it fails
    - `Force`: discharge it immediately without SMT, raising an exception on failure
    - `ForceSMT`: discharge it immediately with SMT, raising an exception on failure
    - `Drop`: drop it, which is unsound

    Read and set with `FStar.Stubs.Tactics.V2.Builtins.get_guard_policy` and `FStar.Stubs.Tactics.V2.Builtins.set_guard_policy`. *)
type guard_policy =
    | Goal      // Add guards as (normal) goals
    | SMT       // Add guards as SMT goals
    | SMTSync   // Send guards to SMT immediately, will *log* errors (not raise) if anything fails
    | Force     // Force guards without SMT, immediately. Raises an exception on failure.
    | ForceSMT  // Force guards with SMT, immediately. Raises an exception on failure.
    | Drop      // Drop guards, clearly unsound! careful!

(* Must be inline, this definition is not there in src/FStar.Tactics.Types *)
(*| A list of issues (errors, warnings and information messages), as returned by the typing primitives of `FStar.Stubs.Tactics.V2.Builtins`.

    See `FStar.Issue.issue`. *)
inline_for_extraction
let issues = list FStar.Issue.issue

(*| The type of references holding a value of type `a` in the local state of a tactic.

    Created with `FStar.Stubs.Tactics.V2.Builtins.alloc`, read with `FStar.Stubs.Tactics.V2.Builtins.read` and updated with `FStar.Stubs.Tactics.V2.Builtins.write`. Updates are not reverted on backtracking. *)
val tref (a:Type) : Type0
