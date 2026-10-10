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
module FStar.PredicateExtensionality
module F = FStar.FunctionalExtensionality
module P = FStar.PropositionalExtensionality

(*| Total, `prop`-valued predicates on `a`. *)
let predicate (a:Type) = a -> Tot prop

(*| Pointwise equivalence of two predicates. *)
let peq (#a:Type) (p1:predicate a) (p2:predicate a) =
  forall x. (p1 x <==> p2 x)

(*| Pointwise equivalent predicates are equal when restricted to the domain
    `a`.

    Combines `FStar.FunctionalExtensionality` with
    `FStar.PropositionalExtensionality`. The predicates themselves may not be
    provably equal, since they may be defined on a larger domain; see
    `FStar.FunctionalExtensionality.on_domain`. *)
let predicateExtensionality (a:Type) (p1 p2:predicate a)
  : Lemma (requires (peq #a p1 p2))
  	  (ensures (F.on_domain a p1==F.on_domain a p2))
  = P.axiom();
    assert (F.feq p1 p2)

