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

(** This module provides some utilities on top of FStar.Sequence *)
module FStar.Sequence.Util
open FStar.Sequence.Base


(*| Returns the elements of `s` from index `i` included to index `j`
    excluded, like a Dafny sequence slice `s[i..j]`.

    The caller must prove `i <= j <= length s`. Defined as
    `drop (take s j) i`. *)
let slice (#ty: Type u#a) (s: seq ty) (i: nat) (j: nat{j >= i && j <= length s})
  : seq ty
  = all_seq_facts_lemma u#a ();
    drop (take s j) i

(*| Returns `s` with `x` added at the front.

    Defined as `append (singleton x) s`. To add an element at the end, use
    `FStar.Sequence.Base.build`. *)
let cons #a (x:a) (s:seq a) = singleton x `append` s

(*| Returns the first element of a nonempty sequence. *)
let head #a (s:seq a{length s > 0}) = s $@ 0

(*| Returns a nonempty sequence without its first element; defined as
    `drop s 1`. *)
let tail #a (s:seq a{length s > 0}) = drop s 1

(*| Splits a nonempty sequence into all but its last element and its last
    element.

    The inverse of `FStar.Sequence.Base.build`. *)
let un_build (#a:_) (s:seq a{length s > 0})
  : seq a & a
  = take s (length s - 1),
    s $@ (length s - 1)

(*| Splits `s` at index `i` into `take s i` and `drop s i`.

    The caller must prove `i <= length s`. *)
let split #a (s:seq a) (i:nat{ i <= length s})
  : seq a & seq a
  = take s i,
    drop s i

(*| Returns the number of elements of `s` that satisfy the predicate `f`.

    See `FStar.Sequence.Util.count` for counting the occurrences of a value. *)
let rec count_matches (#a:Type u#a) (f:a -> bool) (s:seq a)
  : Tot nat (decreases (length s))
  = all_seq_facts_lemma u#a ();
    if length s = 0 then 0
    else if f (head s) then 1 + count_matches f (tail s)
    else count_matches f (tail s)

(*| States that `FStar.Sequence.Util.count_matches` is 0 on an empty
    sequence. *)
let count_matches_empty (a:Type) (f:a -> bool) (s:seq a{length s = 0})
  : Lemma (count_matches f s = 0)
  = ()

(*| Returns the number of occurrences of `x` in `s`;
    `FStar.Sequence.Util.count_matches` with equality to `x`.

    It is opaque to SMT, which gives proofs control over its unfolding: use
    `reveal_opaque` or the lemmas `FStar.Sequence.Util.count_empty`,
    `FStar.Sequence.Util.count_head` and
    `FStar.Sequence.Util.lemma_append_count_aux`. *)
[@@"opaque_to_smt"]
let count (#a:eqtype) (x:a) (s:seq a) = count_matches (fun y -> x = y) s

(*| States that every value occurs 0 times in an empty sequence, as counted
    by `FStar.Sequence.Util.count`. *)
let count_empty (#a:eqtype) (s:seq a{length s = 0})
  : Lemma (forall x. count x s = 0)
  = reveal_opaque (`%count) (count #a)

(*| States that the first element of a nonempty sequence occurs in it at
    least once, as counted by `FStar.Sequence.Util.count`. *)
let count_head (#a:eqtype) (s:seq a{length s > 0})
  : Lemma (count (head s) s > 0)
  = reveal_opaque (`%count) (count #a)

(*| States that the number of occurrences of `x` in `append lo hi` is the
    sum of its occurrences in `lo` and in `hi`. *)
let rec lemma_append_count_aux (#a:eqtype) (x:a) (lo hi:seq a)
  : Lemma
    (ensures (count x (append lo hi) = (count x lo + count x hi)))
    (decreases (length lo))
  = all_seq_facts_lemma();
    reveal_opaque (`%count) (count #a);
    if length lo = 0
    then assert (append lo hi `equal` hi)
    else (
      lemma_append_count_aux x (tail lo) hi;
      assert (append (tail lo) hi `equal` tail (append lo hi))
    )


(*| Combines the elements of `s` with `f`, starting from `init` and the
    first element, so that the last element is applied outermost.

    For a sequence with elements `x0`, `x1`, `x2`, the result is
    `f x2 (f x1 (f x0 init))`; for an empty sequence it is `init`. See also
    `FStar.Sequence.Permutation.foldm_back`. *)
let rec fold_back (#a:Type u#a) (#b:Type u#b) (f:b -> a -> Tot a) (s:seq b) (init:a)
  : Tot a (decreases (length s))
  = all_seq_facts_lemma u#b ();
    if length s = 0 then init
    else let last  = s $@ (length s - 1) in
         let s = take s (length s - 1) in
         f last (fold_back f s init)
