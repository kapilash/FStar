(*
   Copyright 2022 Microsoft Research
   
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

(*
   Here we reason about nested folds of functions over arbitrary 
   integer intervals. We call such functions generators.
*)
 
module FStar.Algebra.CommMonoid.Fold.Nested

module CF = FStar.Algebra.CommMonoid.Fold
module CE = FStar.Algebra.CommMonoid.Equiv

open FStar.IntegerIntervals 

(*| Swaps the two arguments of a two-argument function on integer ranges:
    the result `f` satisfies `f j i == gen i j`.

    Useful to state the exchange of nested folds and transposition of matrices.
    For zero-based domains, `FStar.Matrix.transposed_matrix_gen` is more
    convenient. *)
let transpose_generator #c (#m0 #mk: int)
                          (#n0 #nk: int)
                          (gen: ifrom_ito m0 mk -> ifrom_ito n0 nk -> c)
  : (f: (ifrom_ito n0 nk -> ifrom_ito m0 mk -> c) { forall i j. f j i == gen i j })
  = fun j i -> gen i j
  
(*| Nested fold of a two-argument function `g` over the ranges `[a0, ak]` and
    `[b0, bk]`: the outer fold over `i` of the inner fold over `j` of `g i j`.

    Built from `FStar.Algebra.CommMonoid.Fold.fold`. See
    `FStar.Algebra.CommMonoid.Fold.Nested.double_fold_transpose_lemma` for
    swapping the order of summation. *)
let double_fold #c #eq #a0 (#ak: not_less_than a0) #b0 (#bk:not_less_than b0)
                (cm: CE.cm c eq)
                (g: ifrom_ito a0 ak -> ifrom_ito b0 bk -> c) = 
  CF.fold cm a0 ak (fun (i: ifrom_ito a0 ak) -> CF.fold cm b0 bk (g i))  


(*| Proves that the order of a nested fold can be exchanged: folding over
    `i` then `j` is equivalent, under `eq`, to folding over `j` then `i`.

    The finite version of Fubini's theorem for commutative monoids, stated with
    `FStar.Algebra.CommMonoid.Fold.Nested.transpose_generator`. *)
val double_fold_transpose_lemma (#c:_) (#eq: _)
                                (#m0: int) (#mk: not_less_than m0)
                                (#n0: int) (#nk: not_less_than n0)
                                (cm: CE.cm c eq) 
                                (offset_gen: ifrom_ito m0 mk -> ifrom_ito n0 nk -> c)
  : Lemma (double_fold cm offset_gen
           `eq.eq`            
           double_fold cm (transpose_generator offset_gen))
