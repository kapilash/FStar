(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Guido Martinez, Aseem Rastogi, Nikhil Swamy
*)

module FStar.Calc

open FStar.Preorder

/// This module provides calculational proofs support
///
/// Client programs need not use it directly,
///   instead F* provides convenient syntax for writing calculational proofs
///
/// See examples/calc for some examples

(*| Holds when `x` and `y` are linked by a chain of steps using the relations
    in `rs`, read in reverse order.

    The empty chain relates `x` only to itself. Opaque to SMT. *)
[@@"opaque_to_smt"]
let rec calc_chain_related (#a:Type) (rs:list (relation a)) (x y:a)
  : prop
  = match rs with
    | [] -> x == y
      (* GM: The `:t` annotation below matters a lot for compactness of the formula! *)
    | r1::rs -> exists (w:a). calc_chain_related rs x w /\ r1 w y

(*| Holds when every chain of steps using the relations `rs` implies the
    relation `p`.

    The side condition checked by `FStar.Calc.calc_finish`. Opaque to SMT. *)
[@@"opaque_to_smt"]
let calc_chain_compatible (#t:Type) (rs:list (relation t)) (p:relation t)
  : prop
  = forall (x y:t). calc_chain_related rs x y ==> p x y

(*| A proof-irrelevant witness that `x` and `y` are related by a chain of
    calculational steps using the relations `rs`.

    Users rarely need this module directly: `calc` blocks are desugared into
    `FStar.Calc.calc_init`, `FStar.Calc.calc_step` and `FStar.Calc.calc_finish`.

    ```fstar
    let calc_example (a b: int) (h: squash (a == b)) : Lemma (a + 1 == b + 1) =
      calc (==) {
        a + 1;
        == { }
        b + 1;
      }
    ``` *)
val calc_pack (#a:Type) (rs:list (relation a)) (x y:a) : prop

(*| Starts a calculational proof at `x`, with an empty chain of steps. *)
val calc_init (#a:Type) (x:a) : Tot (calc_pack [] x x)

(*| Extends a calculational proof from `x` to `y` with one step from `y` to `z`
    using the relation `p`.

    `pf` is the proof of the earlier steps and `j` justifies `p y z`. The step
    relation is prepended, so the list of relations is in reverse order. *)
val calc_step
  (#a:Type)
  (#x #y:a)
  (p:relation a)                             (* Relation for this step *)
  (z:a)                                      (* Next expression *)
  (#rs:list (relation a))
  (pf:unit -> Tot (calc_pack rs x y))         (* Rest of the proof *)
  (j:unit -> Tot (squash (p y z)))            (* Justification *)
  : Tot (calc_pack (p::rs) x z)

(*| Concludes a calculational proof from `x` to `y`, establishing `p x y`.

    Requires that the chain of step relations is compatible with `p`; when it
    is not, the failure is reported at the location of the proof. *)
val calc_finish
  (#a:Type)
  (p:relation a)
  (#x #y:a)
  (#rs:list (relation a))
  (pf:unit -> Tot (calc_pack rs x y))
  : Lemma
      (requires (norm [delta_only [`%calc_chain_compatible; `%calc_chain_related];
                       iota;
                       zeta]
                      (Range.labeled (range_of pf)
                         "Could not prove that this calc-chain is compatible"
                         (calc_chain_compatible rs p))))
      (ensures (p x y))

(*| Turns a ghost function from proofs of `p` to proofs of `q` into a proof of
    `p ==> q`.

    Used when desugaring `calc` steps whose relation is `==>`, so that the
    justification of a step may assume its left-hand side. *)
val calc_push_impl (#p #q:prop) (f:squash p -> GTot (squash q))
  : Tot (squash (p ==> q))
