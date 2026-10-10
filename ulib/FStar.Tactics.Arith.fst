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
module FStar.Tactics.Arith

open FStar.Tactics.V2.Bare
open FStar.Reflection.V2.Formula
open FStar.Reflection.V2.Arith

// decide if the current goal is arith, drop the built representation of it
(*| Tactic that tests whether the current goal is an arithmetic proposition.

    It returns `true` when `FStar.Reflection.V2.Arith.is_arith_prop` recognizes
    the goal: equalities and comparisons (`<`, `<=`) between arithmetic
    expressions, and conjunctions and disjunctions of such. The parsed
    representation is discarded. *)
let is_arith_goal () : Tac bool =
    let g = cur_goal () in
    match run_tm (is_arith_prop g) with
    | Inr _ -> true
    | _ -> false

(*| Tactic that splits the current goal along conjunctions, implications and universal quantifiers, and sends the arithmetic parts to SMT in a pruned context.

    On an arithmetic goal (see `FStar.Tactics.Arith.is_arith_goal`), it prunes
    every module from the SMT context except `Prims` and calls
    `FStar.Tactics.V2.Derived.smt`. Otherwise it proves `True` with
    `FStar.Tactics.V2.Derived.trivial`, splits a conjunction, introduces the
    premise of an implication or the variables of a `forall` and recurses
    (reverting the introduced hypotheses afterwards), and leaves any other goal
    unchanged. *)
val split_arith : unit -> Tac unit
let rec split_arith () =
    if is_arith_goal () then
        begin
        prune "";
        addns "Prims";
        smt ()
        end
    else begin
        let g = cur_goal () in
        match term_as_formula g with
        | True_ ->
            trivial ()
        | And l r ->
            seq FStar.Tactics.split split_arith
        | Implies p q ->
            let _ = implies_intro () in
            seq split_arith l_revert
        | Forall _x _sort _p ->
            let bs = forall_intros () in
            seq split_arith (fun () -> l_revert_all bs)
        | _ ->
            ()
    end
