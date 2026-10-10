(*
   Copyright 2008-2025 Microsoft Research

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
module FStar.Tactics.Easy

open FStar.Tactics.Effect
open FStar.Tactics.Logic.Lemmas {} (* needed to bring in lemma_from_squash into tc scope for clients *)

(*| Solves the current goal by introducing all binders with `FStar.Stubs.Tactics.V2.Builtins.intro` and handing the rest to SMT.

    Used as the tactic that fills the implicit argument of
    `FStar.Tactics.Easy.easy`. *)
[@@plugin]
val easy_fill () : Tac unit

(* Call this function to solve any "easy" goals, where we just
have to introduce a bunch of binders and call SMT. *)

(*| Proves an "easy" goal of the expected type: one that only needs its binders introduced and then SMT.

    The implicit argument is synthesized by `FStar.Tactics.Easy.easy_fill`,
    so `easy` can be used directly as the definition of a lemma.

    ```fstar
    let easy_example : x:nat -> Lemma (x + 0 == x) = FStar.Tactics.Easy.easy
    ``` *)
let easy (#a:Type) (#[easy_fill ()] x : a) : a = x
