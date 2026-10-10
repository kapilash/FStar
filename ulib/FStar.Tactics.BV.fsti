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
module FStar.Tactics.BV

open FStar.Tactics.Effect
open FStar.Tactics.BV.Lemmas {} (* bring into tc scope, since the tactic calls the lemmas *)

(*| Tactic that proves a goal `int2bv e == ?z` by pushing `FStar.BV.int2bv` through the arithmetic expression `e`, thereby solving `?z` with an equivalent bit vector expression.

    It focuses on the current goal, unfolds `FStar.BV.bvult`, and requires an
    equality; other goals fail with an "unexpected" error. The left
    side is parsed with `FStar.Reflection.V2.Arith.as_arith_expr`; `logand`,
    `logxor`, `logor`, shifts, `udiv`, `mod`, `mul_mod`, `add` and `sub` are
    rewritten with the `int2bv` lemmas of `FStar.BV` and the congruence lemmas
    of `FStar.Tactics.BV.Lemmas`, and the remaining leaves are closed by
    reflexivity. When the left side cannot be parsed, it dumps the error and
    tries reflexivity. *)
[@@plugin]
val arith_to_bv_tac () : Tac unit

(*| Tactic that proves an equality between two `FStar.UInt.uint_t n` expressions built from bitwise and modular arithmetic operations, by translating it to bit vectors for Z3.

    It applies `FStar.Tactics.BV.Lemmas.eq_to_bv` and
    `FStar.Tactics.BV.Lemmas.trans`, translates both sides with
    `FStar.Tactics.BV.arith_to_bv_tac`, sets `--smtencoding.elim_box true`,
    normalizes with `delta`, and sends the resulting bit vector equality to SMT.

    ```fstar
    let logand_comm (x y: FStar.UInt.uint_t 64) =
      assert (FStar.UInt.logand x y == FStar.UInt.logand y x)
        by (FStar.Tactics.BV.bv_tac ())
    ``` *)
[@@plugin]
val bv_tac () : Tac unit

(*| Tactic that proves `x < y` for `FStar.UInt.uint_t n` expressions by translating it to an unsigned bit vector comparison for Z3; the argument is the width `n`.

    It applies `FStar.Tactics.BV.Lemmas.trans_lt2` at width `n`, translates both
    sides with `FStar.Tactics.BV.arith_to_bv_tac`, sets
    `--smtencoding.elim_box true` and sends the resulting `FStar.BV.bvult`
    goal to SMT. *)
[@@plugin]
val bv_tac_lt (n:int) : Tac unit

(*| Tactic that turns an equality between two `FStar.UInt.uint_t n` expressions into an equality between bit vector expressions, without calling SMT.

    It performs the translation steps of `FStar.Tactics.BV.bv_tac` and leaves
    the bit vector equality as the current goal. *)
[@@plugin]
val to_bv_tac () : Tac unit