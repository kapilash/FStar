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
module FStar.Tactics.Canon

open FStar.Tactics.Effect
open FStar.Tactics.Canon.Lemmas {} (* bring lemmas into tc scope *)

(*| Rewrites every integer arithmetic subterm of the current goal into a normal form, without closing the goal.

    The tactic walks the goal with `FStar.Tactics.V2.Derived.pointwise` and, for each subterm that `FStar.Reflection.V2.Arith.is_arith_expr` recognises as an `int` expression, proves a rewriting step from the lemmas of `FStar.Tactics.Canon.Lemmas`. It evaluates sums and products of literals, distributes multiplication over addition, reassociates sums and products to the left, sorts operands by `FStar.Reflection.V2.Arith.compare_expr`, drops `0` and `1` units, and turns subtraction and negation into addition and multiplication by `-1`. Subterms that are not recognised are left unchanged.

    The normal form is partial: like coefficients are not collected (`a + a` stays as it is), so the rewritten goal is usually left for the SMT solver or another tactic. For a decision procedure on commutative rings, use `FStar.Tactics.CanonCommSemiring.int_semiring`.

    ```fstar
    let canon_example (x y z : int) =
      assert (x * (y + z) == z * x + y * x)
        by (FStar.Tactics.Canon.canon ())
    ``` *)
[@@plugin]
val canon () : Tac unit
