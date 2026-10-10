(*
   Copyright 2008-2023 Microsoft Research

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
module FStar.Stubs.TypeChecker.Core

//
// A stub for using some type definition from FStar.TypeChecker.Core
//

(*| The effect at which a term is typed by the core typechecker: `E_Total` for total terms and `E_Ghost` for ghost (computationally irrelevant) terms.

    Mirrors the compiler's own type. Used in the typing tokens of `FStar.Stubs.Tactics.Types.Reflection` and the typing primitives of `FStar.Stubs.Tactics.V2.Builtins`. *)
type tot_or_ghost = 
  | E_Total
  | E_Ghost

(*| Which side of a relation between two terms to unfold, as suggested by `FStar.Stubs.Tactics.V2.Builtins.maybe_relate_after_unfolding`.

    The constructors are `Left`, `Right`, `Both` and `Neither`. Mirrors the compiler's own type. *)
type unfold_side =
  | Left
  | Right
  | Both
  | Neither
