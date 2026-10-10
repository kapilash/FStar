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
module FStar.Tactics.Canon.Lemmas


(*| Left distributivity of integer multiplication over addition: `x * (y + z) == x * y + x * z`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val distr : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x * (y + z) == x * y + x * z)

(*| Right distributivity of integer multiplication over addition: `(x + y) * z == x * z + y * z`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val distl : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x + y) * z == x * z + y * z)

(*| Associativity of integer addition, reassociating to the left: `x + (y + z) == (x + y) + z`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val ass_plus_l : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x + (y + z) == (x + y) + z)

(*| Associativity of integer multiplication, reassociating to the left: `x * (y * z) == (x * y) * z`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val ass_mult_l : (#x : int) -> (#y : int) -> (#z : int) -> Lemma (x * (y * z) == (x * y) * z)

(*| Commutativity of integer addition: `x + y == y + x`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val comm_plus : (#x : int) -> (#y : int) -> Lemma (x + y == y + x)

(*| Swaps the last two operands of a left-nested integer sum: `(x + y) + z == (x + z) + y`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val sw_plus : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x + y) + z == (x + z) + y)

(*| Swaps the last two operands of a left-nested integer product: `(x * y) * z == (x * z) * y`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val sw_mult : (#x : int) -> (#y : int) -> (#z : int) -> Lemma ((x * y) * z == (x * z) * y)

(*| Commutativity of integer multiplication: `x * y == y * x`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val comm_mult : (#x : int) -> (#y : int) -> Lemma (x * y == y * x)

(*| Transitivity of propositional equality: from `x == y` and `y == z`, proves `x == z`.

    The middle term `y` is the last implicit argument, so applying this lemma to a goal `x == z` leaves the two equalities as new goals with `y` an unresolved unification variable. `FStar.Tactics.Canon.canon` uses it to chain rewriting steps. *)
val trans : (#a:Type) -> (#x:a) -> (#z:a) -> (#y:a) ->
                    squash (x == y) -> squash (y == z) -> Lemma (x == z)

(*| Congruence of integer addition: from `w == y` and `x == z`, proves `w + x == y + z`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. The two hypotheses become new goals. *)
val cong_plus : (#w:int) -> (#x:int) -> (#y:int) -> (#z:int) ->
                squash (w == y) -> squash (x == z) ->
                Lemma (w + x == y + z)

(*| Congruence of integer multiplication: from `w == y` and `x == z`, proves `w * x == y * z`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. The two hypotheses become new goals. *)
val cong_mult : (#w:int) -> (#x:int) -> (#y:int) -> (#z:int) ->
                squash (w == y) -> squash (x == z) ->
                Lemma (w * x == y * z)

(*| Integer negation is multiplication by `-1`: `-x == (-1) * x`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val neg_minus_one : (#x:int) -> Lemma (-x == (-1) * x)

(*| `0` is a right identity of integer addition: `x + 0 == x`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val x_plus_zero : (#x:int) -> Lemma (x + 0 == x)

(*| `0` is a left identity of integer addition: `0 + x == x`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val zero_plus_x : (#x:int) -> Lemma (0 + x == x)

(*| `0` is right-absorbing for integer multiplication: `x * 0 == 0`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val x_mult_zero : (#x:int) -> Lemma (x * 0 == 0)

(*| `0` is left-absorbing for integer multiplication: `0 * x == 0`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val zero_mult_x : (#x:int) -> Lemma (0 * x == 0)

(*| `1` is a right identity of integer multiplication: `x * 1 == x`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val x_mult_one : (#x:int) -> Lemma (x * 1 == x)

(*| `1` is a left identity of integer multiplication: `1 * x == x`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val one_mult_x : (#x:int) -> Lemma (1 * x == x)

(*| Integer subtraction is addition of the negation: `x - y == x + (-y)`.

    Used by `FStar.Tactics.Canon.canon` as a rewriting step; the integers are implicit, so the lemma is applied with `FStar.Tactics.V2.Derived.apply_lemma`. *)
val minus_is_plus : (#x : int) -> (#y : int) -> Lemma (x - y == x + (-y))
