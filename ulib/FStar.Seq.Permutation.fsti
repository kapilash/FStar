(*
   Copyright 2021-2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: N. Swamy, A. Rastogi, A. Rozanov
*)
module FStar.Seq.Permutation

open FStar.Seq

open FStar.IntegerIntervals

(* This module defines a permutation on sequences as a bijection among
   the sequence indices relating equal elements.

   It defines a few utilities to work with such permutations.

   Notably:

   1. Given two sequence with equal element counts, it constructs a
      permutation.

   2. Folding the multiplication of a commutative monoid over a
      sequence and its permutation produces the equivalent results
*)
  
(*| The type of functions from the indices of `s` to the indices of `s`. *)
let index_fun #a (s:seq a) = under (Seq.length s) -> under (Seq.length s)

(*| Holds when the index function `f` is a permutation from `s0` to `s1`: the
    sequences have the same length, `f` is injective, and the element at index
    `i` of `s0` is the element at index `f i` of `s1`.

    The definition is hidden; `FStar.Seq.Permutation.reveal_is_permutation`
    states it. *)
val is_permutation (#a:Type) (s0:seq a) (s1:seq a) (f:index_fun s0) : prop

(*| Unfolds `FStar.Seq.Permutation.is_permutation`: equal lengths, injectivity of
    `f`, and `index s0 i == index s1 (f i)` for every index `i`. *)
val reveal_is_permutation (#a:Type) (s0 s1:seq a) (f:index_fun s0)
  : Lemma (is_permutation s0 s1 f <==>
           (* lengths of the sequences are the same *)
           Seq.length s0 == Seq.length s1 /\
           (* f is injective *)
           (forall x y. {:pattern f x; f y}
             x <> y ==> f x <> f y) /\
           (* and f relates equal items in s0 and s1 *)
           (forall (i:nat{i < Seq.length s0}).{:pattern (Seq.index s1 (f i))}
              Seq.index s0 i == Seq.index s1 (f i)))

(*| The type of index functions that are permutations from `s0` to `s1`, in the
    sense of `FStar.Seq.Permutation.is_permutation`. *)
let seqperm (#a:Type) (s0:seq a) (s1:seq a) =
  f:index_fun s0 { is_permutation s0 s1 f }

(*| Builds an explicit permutation from `s0` to `s1` when every element occurs
    the same number of times in both (as measured by
    `FStar.Seq.Properties.count`). *)
val permutation_from_equal_counts
      (#a:eqtype)
      (s0:seq a) (s1:seq a{(forall x. count x s0 == count x s1)})
  : Tot (seqperm s0 s1)

(** Now, some utilities related to commutative monoids and permutations *)

module CE = FStar.Algebra.CommMonoid.Equiv

(*| Combines all elements of `s` with the operation of the commutative monoid
    `m`, starting from its unit. Defined with `FStar.Seq.Properties.foldr_snoc`.

    The lemmas of this module state results up to the monoid's equivalence `eq`. *)
let foldm_snoc (#a:Type) (#eq:CE.equiv a) (m:CE.cm a eq) (s:seq a) =
  foldr_snoc m.mult s m.unit

(*| Folding a sequence whose elements are all the unit gives the unit, up to
    `eq`. *)
val foldm_snoc_unit_seq (#a:Type) (#eq:CE.equiv a) (m:CE.cm a eq) (s:Seq.seq a)
  : Lemma (requires Seq.equal s (Seq.create (Seq.length s) m.unit))
          (ensures eq.eq (foldm_snoc m s) m.unit)

(*| Folding a one-element sequence gives that element, up to `eq`. *)
val foldm_snoc_singleton (#a:_) (#eq:_) (m:CE.cm a eq) (x:a)
  : Lemma (eq.eq (foldm_snoc m (Seq.create 1 x)) x)

(*| The fold of `append s1 s2` is the product of the folds of `s1` and `s2`, up
    to `eq`. *)
val foldm_snoc_append (#a:Type) (#eq:CE.equiv a) (m:CE.cm a eq) (s1 s2: seq a)
  : Lemma
    (ensures eq.eq (foldm_snoc m (append s1 s2))
                   (m.mult (foldm_snoc m s1) (foldm_snoc m s2)))

(*| The fold of `append s1 s2` equals the fold of `append s2 s1`, up to `eq`. *)
val foldm_snoc_sym (#a:Type) (#eq:CE.equiv a) (m:CE.cm a eq) (s1 s2: seq a)
  : Lemma
    (ensures eq.eq (foldm_snoc m (append s1 s2))
                   (foldm_snoc m (append s2 s1)))

(*| Folding is invariant under permutation: given a permutation `p` from `s0` to
    `s1`, their folds are equal up to `eq`.

    Use `FStar.Seq.Permutation.permutation_from_equal_counts` to obtain `p` from
    equal element counts. *)
val foldm_snoc_perm (#a:_) (#eq:_)
               (m:CE.cm a eq)
               (s0:seq a)
               (s1:seq a)
               (p:seqperm s0 s1)
  : Lemma
    (ensures eq.eq (foldm_snoc m s0) (foldm_snoc m s1))

/// foldm_snoc_split:  This next bit is for a lemma that proves that if
///   if the fold is taken over a sequence of sums, it is equal
///   to a sum of folds of the summand sequences
  
(*| Turns a function on the integer range `[n0, nk]` into an initializer for
    `FStar.Seq.Base.init`: index `i` is mapped to `expr (n0 + i)`.

    The arguments `a` and `b` only bound the indices to `closed_interval_size a b`;
    the offset is `n0`, not `a`. *)
let init_func_from_expr #c (#n0: int) (#nk: not_less_than n0)
                        (expr: ifrom_ito n0 nk -> c)
                        (a: ifrom_ito n0 nk)
                        (b: ifrom_ito a nk)
                        (i: under (closed_interval_size a b))
  : c
  = expr (n0+i)

(*| The pointwise product of `f` and `g` under the operation of the commutative
    monoid `cm`. *)
let func_sum #a #c #eq (cm: CE.cm c eq) (f g: a -> c)
  : t:(a -> c){ forall (x:a). t x == f x `cm.mult` g x }
  = fun (x:a) -> cm.mult (f x) (g x)

open FStar.Seq.Equiv

(*| The fold over a range `[n0, nk]` of the pointwise product of `expr1` and
    `expr2` equals, up to `eq`, the product of the two separate folds.

    The sequences are built with `FStar.Seq.Base.init` and
    `FStar.Seq.Permutation.init_func_from_expr`. *)
val foldm_snoc_split (#c:_) (#eq:_)
                     (cm: CE.cm c eq)
                     (n0: int)
                     (nk: not_less_than n0)
                     (expr1 expr2: (ifrom_ito n0 nk) -> c)
  : Lemma (ensures (foldm_snoc cm (init (closed_interval_size n0 nk) (init_func_from_expr (func_sum cm expr1 expr2) n0 nk)) `eq.eq`
           cm.mult (foldm_snoc cm (init (closed_interval_size n0 nk) (init_func_from_expr expr1 n0 nk)))
                   (foldm_snoc cm (init (closed_interval_size n0 nk) (init_func_from_expr expr2 n0 nk)))))



(*| Sequences that are equivalent element-wise (`FStar.Seq.Equiv.eq_of_seq`) have
    equivalent folds. *)
val foldm_snoc_equality (#c:_) (#eq:_) (add: CE.cm c eq) (s t: seq c)
  : Lemma (requires length s == length t /\ eq_of_seq eq s t)
          (ensures foldm_snoc add s `eq.eq` foldm_snoc add t) 


(*| If each element of `sum_seq` is equivalent to the product of the elements of
    `s` and `t` at the same index, then the product of the folds of `s` and `t`
    is equivalent to the fold of `sum_seq`.

    The element-wise fact is passed as the lemma `proof`. *)
val foldm_snoc_split_seq (#c:_) (#eq:_) (add: CE.cm c eq) 
                         (s: seq c) (t: seq c{length s == length t})
                         (sum_seq: seq c{length sum_seq == length s})
                         (proof: (i: under (length s)) 
                                 -> Lemma ((index s i `add.mult` index t i)
                                          `eq.eq` (index sum_seq i)))
  : Lemma ((foldm_snoc add s `add.mult` foldm_snoc add t) `eq.eq`
           (foldm_snoc add sum_seq))
           
(*| Folds of `init m f` and `init m g` are equivalent when `f i` and `g i` are
    equivalent for every `i`. *)
val foldm_snoc_of_equal_inits (#c:_) (#eq:_) (#m: pos) (cm: CE.cm c eq) 
                              (f: (under m) -> c) (g: (under m) -> c)
  : Lemma (requires  (forall (i: under m). f i `eq.eq` g i))
          (ensures foldm_snoc cm (init m f) `eq.eq` foldm_snoc cm (init m g))

(*| Unfolds one step of `FStar.Seq.Permutation.foldm_snoc`: the fold of a
    non-empty sequence is the product of its last element and the fold of its
    prefix (an equality, not just an equivalence).

    Calling it explicitly can speed up large proofs. *)
let foldm_snoc_decomposition #c #eq (cm: CE.cm c eq) 
                             (s: seq c{length s > 0})
  : Lemma (foldm_snoc cm s == 
           cm.mult (snd (un_snoc s)) (foldm_snoc cm (fst (un_snoc s)))) = ()
