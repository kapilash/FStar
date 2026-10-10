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
module FStar.Preorder

(* Preordered relations and stable predicates *)

(*| Binary, `prop`-valued relations on `a`. *)
type relation (a:Type) = a -> a -> prop

(*| `prop`-valued predicates on `a`. *)
type predicate (a:Type) = a -> prop

(*| The relation `rel` relates every value to itself. *)
let reflexive (#a:Type) (rel:relation a) =
  forall (x:a). rel x x

(*| The relation `rel` is transitive. *)
let transitive (#a:Type) (rel:relation a) =
  forall (x:a) (y:a) (z:a). (rel x y /\ rel y z) ==> rel x z

(*| The relation `rel` is a preorder: reflexive and transitive. *)
let preorder_rel (#a:Type) (rel:relation a) =
  reflexive rel /\ transitive rel

(*| Preorders on `a`: relations that are reflexive and transitive. *)
type preorder (a:Type) = rel:relation a{preorder_rel rel}

(*| The predicate `p` is preserved by the preorder `rel`: if `p x` holds and
    `rel x y`, then `p y` holds.

    Stable predicates remain true as a value evolves along the preorder, as is
    typical for monotonic state. *)
let stable (#a:Type) (p:predicate a) (rel:relation a{preorder_rel rel}) =
  forall (x:a) (y:a). (p x /\ rel x y) ==> p y
