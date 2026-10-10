(*
   Copyright 2008-2022 Microsoft Research
   
   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
   
       http://www.apache.org/licenses/LICENSE-2.0
       
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: A. Rozanov
*)

module FStar.Algebra.CommMonoid.Fold
module CE = FStar.Algebra.CommMonoid.Equiv

open FStar.Seq.Base
open FStar.Seq.Properties 
open FStar.Seq.Permutation

open FStar.IntegerIntervals


(* Here we define the notion for big sums and big products for 
   arbitrary commutative monoids. We construct the folds from 
   an integer range and a function, then calculate the fold --
   a sum or a product, depending on the monoid operation. *)
 
(* We refine multiplication a bit to make proofs smoothier *)


(* Notice how we can't just use a and b if we don't want to break 
   recursive calls with the same exprs *)
(*| Turns a function on the integer range `[n0, nk]` into a zero-based function
    suitable for `FStar.Seq.Base.init` over a range of the size of `[a, b]`.

    Index `i` maps to `expr (n0 + i)`: the offset is the lower bound `n0` of the
    domain of `expr`, not `a`, so with `a = n0` the result enumerates `expr a`,
    ..., `expr b`. Used to state `FStar.Algebra.CommMonoid.Fold.fold_equals_seq_foldm`. *)
let init_func_from_expr #c (#n0: int) (#nk: not_less_than n0) 
                        (expr: (ifrom_ito n0 nk) -> c) 
                        (a: ifrom_ito n0 nk) (b: ifrom_ito a nk) 
  : (counter_for (ifrom_ito a b) -> c)
  = fun (i: counter_for (ifrom_ito a b)) -> expr (n0 + i)

(*| Folds a commutative monoid over a function on a closed integer range: the
    big sum or big product `expr a` `cm.mult` ... `cm.mult` `expr b`.

    The range `[a, b]` is never empty (`b >= a`), and the result is left-nested:
    `fold cm a b expr` is `cm.mult (fold cm a (b-1) expr) (expr b)` when `b > a`,
    and `expr a` when `b = a`. The definition is hidden; reason about it with
    `FStar.Algebra.CommMonoid.Fold.fold_singleton_lemma`,
    `FStar.Algebra.CommMonoid.Fold.fold_snoc_decomposition` and the other lemmas
    of this module. Proofs are sensitive to the domain of `expr`: give it
    exactly the type `ifrom_ito a b -> c`, and pass the same function term (for
    instance a named function) to every lemma.

    ```fstar
    let id_int (i: int) : int = i

    let sum_0_to_2 () : Lemma (CF.fold CE.int_plus_cm 0 2 id_int == 3) =
      CF.fold_snoc_decomposition CE.int_plus_cm 0 2 id_int;
      CF.fold_snoc_decomposition CE.int_plus_cm 0 1 id_int;
      CF.fold_singleton_lemma CE.int_plus_cm 0 id_int
    ``` *)
val fold (#c:_) (#eq:_) (cm: CE.cm c eq)
         (a: int) (b: not_less_than a) (expr: ifrom_ito a b -> c) : c
  
(*| Proves that folds of two functions over the same range are equal (`==`)
    when the functions agree on every point of the range. *)
val fold_equality (#c:_) (#eq:_) (cm: CE.cm c eq) 
                  (a: int) (b: not_less_than a) 
                  (expr1 expr2: (ifrom_ito a b) -> c)
  : Lemma (requires (forall (i: ifrom_ito a b). expr1 i == expr2 i))
          (ensures fold cm a b expr1 == fold cm a b expr2) 

(*| Proves that the fold over the one-point range `[a, a]` is `expr a`. *)
val fold_singleton_lemma (#c:_) (#eq:_) (cm:CE.cm c eq) 
                         (a:int) (expr: ifrom_ito a a -> c)
  : Lemma (fold cm a a expr == expr a) 

(*| Proves that a fold over `[a, b]` with `b > a` is the fold over `[a, b-1]`
    combined by `cm.mult` with the last term `expr b`.

    This is the defining equation of `FStar.Algebra.CommMonoid.Fold.fold`, and
    holds with `==`. *)
val fold_snoc_decomposition (#c:_) (#eq:_) 
                            (cm: CE.cm c eq) 
                            (a: int) (b: greater_than a) 
                            (expr: (ifrom_ito a b) -> c) 
  : Lemma (fold cm a b expr == fold cm a (b-1) expr `cm.mult` (expr b))

(*| Proves that the fold over `[a, b]` is equivalent, under `eq`, to
    `FStar.Seq.Permutation.foldm_snoc` of the sequence of `expr a`, ..., `expr b`.

    Use it to transfer the sequence lemmas of `FStar.Seq.Permutation` (for
    example, invariance under permutation) to range folds. *)
val fold_equals_seq_foldm (#c:_) (#eq:_) 
                          (cm: CE.cm c eq) 
                          (a: int) 
                          (b: not_less_than a) 
                          (expr: (ifrom_ito a b) -> c)
  : Lemma (ensures fold cm a b expr `eq.eq` 
                   foldm_snoc cm (init (closed_interval_size a b) 
                                       (init_func_from_expr expr a b)))
    
(*| Proves that two folds over ranges of the same length are equal (`==`) when
    the functions agree after shifting: `expr1 (i + m0) == expr2 (i + n0)` for
    every offset `i` in the range.

    The bounds are explicit so that the lemma can be applied to subranges. *)
val fold_offset_irrelevance_lemma (#c:_) (#eq:_) (cm: CE.cm c eq) 
                                  (m0: int) (mk: not_less_than m0) 
                                  (expr1 : ifrom_ito m0 mk -> c)
                                  (n0: int) (nk: not_less_than n0) 
                                  (expr2 : ifrom_ito n0 nk -> c)
  : Lemma (requires (((mk-m0) = (nk-n0)) /\ 
                     (forall (i:under (closed_interval_size m0 mk)). 
                        expr1 (i+m0) == expr2 (i+n0))))
          (ensures fold cm m0 mk expr1 == fold cm n0 nk expr2) 

(*| Proves that a fold over `[m0, mk]` equals (`==`) the fold over the
    zero-based range `[0, mk - m0]` of a function `expr2` with
    `expr2 i == expr1 (i + m0)`.

    A special case of `FStar.Algebra.CommMonoid.Fold.fold_offset_irrelevance_lemma`. *)
val fold_offset_elimination_lemma (#c:_) (#eq:_) (cm: CE.cm c eq) 
                                  (m0: int) (mk: not_less_than m0) 
                                  (expr1 : ifrom_ito m0 mk -> c)
                                  (expr2 : under (closed_interval_size m0 mk) -> c)
  : Lemma (requires ((forall (i:under (closed_interval_size m0 mk)). 
                         expr2 i == expr1 (i+m0))))
          (ensures fold cm m0 mk expr1 == fold cm 0 (mk-m0) expr2)
