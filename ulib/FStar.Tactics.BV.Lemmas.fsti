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
module FStar.Tactics.BV.Lemmas

open FStar.BV
open FStar.UInt

// using uint_t' instead of uint_t breaks the tactic (goes to inl).

(* Congruence lemmas *)
(*| Congruence of `FStar.BV.bvand`: if `w == y` and `x == z` then `bvand w x == bvand y z`.

    Used by `FStar.Tactics.BV.arith_to_bv_tac` to rewrite both operands. *)
val cong_bvand : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
                   (#y:bv_t n) -> (#z:bv_t n) ->
                   squash (w == y) -> squash (x == z) ->
                   Lemma (bvand #n w x == bvand #n y z)

(*| Congruence of `FStar.BV.bvxor`: if `w == y` and `x == z` then `bvxor w x == bvxor y z`.

    Used by `FStar.Tactics.BV.arith_to_bv_tac` to rewrite both operands. *)
val cong_bvxor : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
                   (#y:bv_t n) -> (#z:bv_t n) ->
                   squash (w == y) -> squash (x == z) ->
                   Lemma (bvxor w x == bvxor y z)

(*| Congruence of `FStar.BV.bvor`: if `w == y` and `x == z` then `bvor w x == bvor y z`.

    Used by `FStar.Tactics.BV.arith_to_bv_tac` to rewrite both operands. *)
val cong_bvor : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
                   (#y:bv_t n) -> (#z:bv_t n) ->
                   squash (w == y) -> squash (x == z) ->
                   Lemma (bvor w x == bvor y z)

(*| Congruence of `FStar.BV.bvshl` in its bit vector argument: if `w == y` then `bvshl w x == bvshl y x`.

    The second argument `x` is a shift amount and stays unchanged. Used by
    `FStar.Tactics.BV.arith_to_bv_tac`. *)
val cong_bvshl : #n:pos -> (#w:bv_t n) -> (#x:uint_t n) ->
                 (#y:bv_t n) -> squash (w == y) ->
                 Lemma (bvshl w x == bvshl y x)

(*| Congruence of `FStar.BV.bvshr` in its bit vector argument: if `w == y` then `bvshr w x == bvshr y x`.

    The second argument `x` is a shift amount and stays unchanged. Used by
    `FStar.Tactics.BV.arith_to_bv_tac`. *)
val cong_bvshr : #n:pos -> #w:bv_t n -> (#x:uint_t n) ->
               #y:bv_t n -> squash (w == y) ->
               Lemma (bvshr #n w x == bvshr #n y x)

(*| Congruence of `FStar.BV.bvdiv` in its bit vector argument: if `w == y` then `bvdiv w x == bvdiv y x`.

    The second argument `x` is a nonzero `FStar.UInt.uint_t n` divisor and stays unchanged. Used by
    `FStar.Tactics.BV.arith_to_bv_tac`. *)
val cong_bvdiv : #n:pos -> #w:bv_t n -> (#x:uint_t n{x <> 0}) ->
              #y:bv_t n -> squash (w == y) ->
               Lemma (bvdiv #n w x == bvdiv #n y x)

(*| Congruence of `FStar.BV.bvmod` in its bit vector argument: if `w == y` then `bvmod w x == bvmod y x`.

    The second argument `x` is a nonzero `FStar.UInt.uint_t n` divisor and stays unchanged. Used by
    `FStar.Tactics.BV.arith_to_bv_tac`. *)
val cong_bvmod : #n:pos -> #w:bv_t n -> (#x:uint_t n{x <> 0}) ->
              #y:bv_t n -> squash (w == y) ->
               Lemma (bvmod #n w x == bvmod #n y x)

(*| Congruence of `FStar.BV.bvmul` in its bit vector argument: if `w == y` then `bvmul w x == bvmul y x`.

    The second argument `x` is a `FStar.UInt.uint_t n` factor and stays unchanged. Used by
    `FStar.Tactics.BV.arith_to_bv_tac`. *)
val cong_bvmul : #n:pos -> #w:bv_t n -> (#x:uint_t n) ->
              #y:bv_t n -> squash (w == y) ->
               Lemma (bvmul #n w x == bvmul #n y x)

(*| Congruence of `FStar.BV.bvadd`: if `w == y` and `x == z` then `bvadd w x == bvadd y z`.

    Used by `FStar.Tactics.BV.arith_to_bv_tac` to rewrite both operands. *)
val cong_bvadd : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
              (#y:bv_t n) -> (#z:bv_t n) ->
              squash (w == y) -> squash (x == z) ->
              Lemma (bvadd w x == bvadd y z)

(*| Congruence of `FStar.BV.bvsub`: if `w == y` and `x == z` then `bvsub w x == bvsub y z`.

    Used by `FStar.Tactics.BV.arith_to_bv_tac` to rewrite both operands. *)
val cong_bvsub : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
              (#y:bv_t n) -> (#z:bv_t n) ->
              squash (w == y) -> squash (x == z) ->
              Lemma (bvsub w x == bvsub y z)

(* Used to reduce the initial equation to an equation on bitvectors*)
(*| Two `FStar.UInt.uint_t n` values are equal when their bit vector images under `FStar.BV.int2bv` are equal.

    Used by `FStar.Tactics.BV.bv_tac` to turn an equation on integers into one
    on bit vectors. *)
val eq_to_bv: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) ->
              squash (int2bv #n x == int2bv #n y) -> Lemma (x == y)

(*| `x < y` holds for `FStar.UInt.uint_t n` values when `FStar.BV.bvult` holds of their images under `FStar.BV.int2bv`. *)
val lt_to_bv: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) ->
              bvult #n (int2bv #n x) (int2bv #n y) -> Lemma (x < y)

(* Creates two fresh variables and two equations of the form int2bv
   x = z /\ int2bv y = w. The above lemmas transform these two
   equations before finally instantiating them through reflexivity,
   leaving Z3 to solve z = w *)
(*| Proves `x == y` from `x == z`, `y == w` and `z == w`.

    `FStar.Tactics.BV.bv_tac` applies it with fresh `z` and `w`: the first two
    premises are solved by `FStar.Tactics.BV.arith_to_bv_tac`, which instantiates
    `z` and `w` with bit vector expressions, leaving `z == w` to Z3. *)
val trans: #n:pos -> (#x:bv_t n) -> (#y:bv_t n) -> (#z:bv_t n) -> (#w:bv_t n) ->
          squash (x == z) -> squash (y == w) -> squash (z == w) ->
          Lemma (x == y)

(*| Proves `bvult x y` from `x == z`, `y == w` and `bvult z w`.

    The variant of `FStar.Tactics.BV.Lemmas.trans` for unsigned comparison of
    bit vectors. *)
val trans_lt: #n:pos -> (#x:bv_t n) -> (#y:bv_t n) -> (#z:bv_t n) -> (#w:bv_t n) ->
          (eq2 #(bv_t n) x z) -> (eq2 #(bv_t n) y w) -> squash (bvult #n z w) ->
          Lemma (bvult #n x y)

(*| Proves `x < y` on `FStar.UInt.uint_t n` from `int2bv x == z`, `int2bv y == w` and `bvult z w`.

    Used by `FStar.Tactics.BV.bv_tac_lt`, which instantiates `z` and `w` with
    bit vector expressions and leaves `bvult z w` to Z3. *)
val trans_lt2: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) -> (#w:bv_t n) ->
          squash (int2bv #n x == z) -> squash (int2bv #n y == w) -> squash (bvult #n z w) ->
          Lemma (x < y)