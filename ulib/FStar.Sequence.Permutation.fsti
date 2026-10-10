(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: N. Swamy
*)
module FStar.Sequence.Permutation
open FStar.Sequence
open FStar.Sequence.Util
module S = FStar.Sequence
(* This module defines a permutation on sequences as a bijection among
   the sequence indices relating equal elements.

   It defines a few utilities to work with such permutations.

   Notably:

   1. Given two sequence with equal element counts, it constructs a
      permutation.

   2. Folding the multiplication of a commutative monoid over a
      sequence and its permutation produces the same result
*)

(*| The natural numbers strictly less than `n`, that is, the valid indices
    of a sequence of length `n`.

    Despite the name, `n` itself is excluded. *)
let nat_at_most (n:nat) = m:nat { m < n }

(*| The type of functions from the indices of the sequence `s` to indices of
    `s`.

    A candidate permutation of `s`; see
    `FStar.Sequence.Permutation.is_permutation`. *)
let index_fun #a (s:seq a) = nat_at_most (S.length s) -> nat_at_most (S.length s)

(*| Holds when `f` maps the indices of `s0` to those of `s1` as a
    permutation: the sequences have the same length, `f` is injective, and
    `index s0 i == index s1 (f i)` for each index `i`.

    The predicate is abstract;
    `FStar.Sequence.Permutation.reveal_is_permutation` states this
    definition. *)
val is_permutation (#a:Type) (s0:seq a) (s1:seq a) (f:index_fun s0) : prop

(*| States the definition of `FStar.Sequence.Permutation.is_permutation`:
    equal lengths, an injective `f`, and `f` relating equal elements of `s0`
    and `s1`.

    Call it to unfold or to establish `is_permutation s0 s1 f`. *)
val reveal_is_permutation (#a:Type) (s0 s1:seq a) (f:index_fun s0)
  : Lemma (is_permutation s0 s1 f <==>
           (* lengths of the sequences are the same *)
           S.length s0 == S.length s1 /\
           (* f is injective *)
           (forall x y. {:pattern f x; f y}
             x <> y ==> f x <> f y) /\
           (* and f relates equal items in s0 and s1 *)
           (forall (i:nat{i < S.length s0}).{:pattern (S.index s1 (f i))}
              S.index s0 i == S.index s1 (f i)))

(*| The type of permutations from `s0` to `s1`: index functions of `s0` that
    satisfy `FStar.Sequence.Permutation.is_permutation s0 s1`. *)
let seqperm (#a:Type) (s0:seq a) (s1:seq a) =
  f:index_fun s0 { is_permutation s0 s1 f }

(*| Builds a permutation from `s0` to `s1` when every value occurs as often
    in `s0` as in `s1`, as counted by `FStar.Sequence.Util.count`.

    The element type must have decidable equality. *)
val permutation_from_equal_counts
      (#a:eqtype)
      (s0:seq a) (s1:seq a{(forall x. count x s0 == count x s1)})
  : Tot (seqperm s0 s1)

(** Now, some utilities related to commutative monoids and permutations *)

module CM = FStar.Algebra.CommMonoid

(*| Combines the elements of a sequence with the operation of the
    commutative monoid `m`, starting from its unit.

    It is `FStar.Sequence.Util.fold_back` applied to `m.mult` and `m.unit`;
    the result for an empty sequence is `m.unit`. *)
let foldm_back (#a:Type) (m:CM.cm a) (s:seq a) = fold_back m.mult s m.unit

(*| States that folding a commutative monoid over `append s1 s2` gives the
    monoid product of the folds over `s1` and over `s2`. *)
val foldm_back_append (#a:Type) (m:CM.cm a) (s1 s2: seq a)
  : Lemma
    (ensures foldm_back m (append s1 s2) == m.mult (foldm_back m s1) (foldm_back m s2))

(*| States that folding a commutative monoid over `append s1 s2` gives the
    same result as over `append s2 s1`. *)
val foldm_back_sym (#a:Type) (m:CM.cm a) (s1 s2: seq a)
  : Lemma
    (ensures foldm_back m (append s1 s2) == foldm_back m (append s2 s1))

(*| States that folding a commutative monoid gives the same result over `s0`
    and over any sequence `s1` related to it by a permutation `p`.

    To obtain `p` from equal element counts, use
    `FStar.Sequence.Permutation.permutation_from_equal_counts`. *)
val foldm_back_perm (#a:_)
               (m:CM.cm a)
               (s0:seq a)
               (s1:seq a)
               (p:seqperm s0 s1)
  : Lemma
    (ensures foldm_back m s0  == foldm_back m s1)
