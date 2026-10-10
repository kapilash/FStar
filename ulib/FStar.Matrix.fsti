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
   In this module we provide basic definitions to work with matrices via
   seqs, and define transpose transform together with theorems that assert
   matrix fold equality of original and transposed matrices.
*)


module FStar.Matrix

module CE = FStar.Algebra.CommMonoid.Equiv
module CF = FStar.Algebra.CommMonoid.Fold
module SP = FStar.Seq.Permutation
module SB = FStar.Seq.Base
module ML = FStar.Math.Lemmas

open FStar.IntegerIntervals   

(*| The type of functions that define an `m` by `n` matrix: `gen i j` is the
    element at row `i` and column `j`, with zero-based indices.

    The two-dimensional analogue of the function passed to
    `FStar.Seq.Base.init`; build a matrix from it with `FStar.Matrix.init`. *)
type matrix_generator c (m n: pos) = under m -> under n -> c

(*| The abstract type of `m` by `n` matrices with elements of type `c`, both
    dimensions positive.

    A matrix is stored as a flat, row-major sequence of length `m*n`; see
    `FStar.Matrix.seq_of_matrix` and `FStar.Matrix.matrix_of_seq`. Access
    elements with `FStar.Matrix.ijth` and build matrices with
    `FStar.Matrix.init`. Equivalence of matrices is
    `FStar.Matrix.matrix_equiv`. *)
val matrix (c:Type u#a) (m n : pos) : Type u#a

(*| Proves that the row-major flattened index `i*n + j` of a valid pair of
    indices is below `m*n`. *)
let flattened_index_is_under_flattened_size (m n: pos) (i: under m) (j: under n) 
  : Lemma ((((i*n)+j)) < m*n) = assert (i*n <= (m-1)*n)

(*| Returns the row-major flattened index `i*n + j` of the element at row `i`
    and column `j` of an `m` by `n` matrix.

    The inverse is given by `FStar.Matrix.get_i` and `FStar.Matrix.get_j`. *)
let get_ij (m n: pos) (i:under m) (j: under n) : under (m*n) 
  = flattened_index_is_under_flattened_size m n i j; i*n + j 

(*| Returns the row index `ij / n` of the flattened index `ij` in an `m` by `n`
    matrix. *)
let get_i (m n: pos) (ij: under (m*n)) : under m = ij / n
(*| Returns the column index `ij % n` of the flattened index `ij` in an `m` by
    `n` matrix. *)
let get_j (m n: pos) (ij: under (m*n)) : under n = ij % n

(*| Proves that `FStar.Matrix.get_i` and `FStar.Matrix.get_j` recover the row and
    column from the flattened index `get_ij m n i j`. *)
let consistency_of_i_j (m n: pos) (i: under m) (j: under n) 
  : Lemma (get_i m n (get_ij m n i j) = i /\ get_j m n (get_ij m n i j) = j) = 
  flattened_index_is_under_flattened_size m n i j; //speeds up the proof
  ML.lemma_mod_plus j i n;
  ML.lemma_div_plus j i n 
  
(*| Proves that `FStar.Matrix.get_ij` recovers a flattened index from its row and
    column, as computed by `FStar.Matrix.get_i` and `FStar.Matrix.get_j`. *)
let consistency_of_ij (m n: pos) (ij: under (m*n)) 
  : Lemma (get_ij m n (get_i m n ij) (get_j m n ij) == ij) = ()

(*| Maps the flattened index of an element of an `m` by `n` matrix to the
    flattened index of the same element in the transposed `n` by `m` matrix.

    It is a bijection; see `FStar.Matrix.ji_is_transpose_of_ij` and
    `FStar.Matrix.dual_indices`. *)
let transpose_ji (m n: pos) (ij: under (m*n)) : under (n*m) =  
  flattened_index_is_under_flattened_size n m (get_j m n ij) (get_i m n ij);
  (get_j m n ij)*m + (get_i m n ij)

(*| An arithmetic lemma: for `i < m`, `(j*m + i) % m = i` and `(j*m + i) / m = j`. *)
let indices_transpose_lemma (m: pos) (i: under m) (j: nat) 
  : Lemma (((j*m+i)%m=i) && ((j*m+i)/m=j)) = ML.lemma_mod_plus i j m
 
(*| Proves that `FStar.Matrix.transpose_ji` is an involution: transposing a
    flattened index twice gives it back. *)
let ji_is_transpose_of_ij (m n: pos) (ij: under (m*n)) 
  : Lemma (transpose_ji n m (transpose_ji m n ij) = ij) = 
  indices_transpose_lemma m (get_i m n ij) (get_j m n ij)
   
(*| Proves that `FStar.Matrix.transpose_ji` swaps the row and column of a
    flattened index. *)
let dual_indices (m n: pos) (ij: under (m*n)) : Lemma (
     (get_j n m (transpose_ji m n ij) = get_i m n ij) /\
     (get_i n m (transpose_ji m n ij) = get_j m n ij)) 
  = consistency_of_ij m n ij;
    indices_transpose_lemma m (get_i m n ij) (get_j m n ij)  

(*| Returns the elements of a matrix as a flat sequence of length `m*n`, in
    row-major order.

    The element at row `i` and column `j` is at index `get_ij m n i j`; see
    `FStar.Matrix.ijth_lemma`. *)
val seq_of_matrix : (#c: Type) -> (#m:pos) -> (#n:pos) -> (mx: matrix c m n) -> 
  (s:SB.seq c {
    SB.length s=m*n /\
    (forall (ij: under (m*n)). SB.index s ij == SB.index s (get_ij m n (get_i m n ij) (get_j m n ij)))
  })

(*| Returns the element at row `i` and column `j` of a matrix (zero-based).

    Its refinement relates it to `FStar.Matrix.seq_of_matrix`. *)
val ijth : (#c:Type) -> (#m:pos) -> (#n:pos) -> (mx: matrix c m n) -> (i: under m) -> (j: under n) ->
  (t:c{t == SB.index (seq_of_matrix mx) (get_ij m n i j)})

(*| Proves that `ijth mx i j` is the element of `seq_of_matrix mx` at the
    flattened index `get_ij m n i j`. *)
val ijth_lemma : (#c:Type) -> (#m:pos) -> (#n:pos) -> (mx: matrix c m n) -> (i: under m) -> (j: under n) ->
  Lemma (ijth mx i j == SB.index (seq_of_matrix mx) (get_ij m n i j))

(*| Builds an `m` by `n` matrix from a flat, row-major sequence of length `m*n`. *)
val matrix_of_seq : (#c: Type) -> (m:pos) -> (n:pos) -> (s: SB.seq c{SB.length s = m*n}) -> matrix c m n

(*| The type of `m` by `n` matrices whose elements are given by the generator
    `gen`, both through `FStar.Matrix.ijth` and through
    `FStar.Matrix.seq_of_matrix`.

    The result type of `FStar.Matrix.init`. *)
type matrix_of #c (#m #n: pos) (gen: matrix_generator c m n) = z:matrix c m n {
  (forall (i: under m) (j: under n). ijth z i j == gen i j) /\ 
  (forall (ij: under (m*n)). (SB.index (seq_of_matrix z) ij) == (gen (get_i m n ij) (get_j m n ij)))  
}

(*| Folds a commutative monoid over all the elements of a matrix, as over its
    flat sequence.

    `FStar.Matrix.matrix_fold_equals_fold_of_seq` relates it to
    `FStar.Seq.Permutation.foldm_snoc`; other lemmas express it as a nested
    fold over rows and columns, or over the transposed matrix. *)
val foldm : (#c:Type) -> (#eq:CE.equiv c) -> (#m:pos) -> (#n:pos) -> (cm: CE.cm c eq) -> (mx:matrix c m n) -> c

(*| Proves that `foldm cm mx` is equivalent, under `eq`, to
    `FStar.Seq.Permutation.foldm_snoc` of `seq_of_matrix mx`.

    Triggered automatically on `foldm cm mx`. *)
val matrix_fold_equals_fold_of_seq : 
  (#c:Type) -> (#eq:CE.equiv c) -> (#m:pos) -> (#n:pos) -> (cm: CE.cm c eq) -> (mx:matrix c m n) 
  -> Lemma (ensures foldm cm mx `eq.eq` SP.foldm_snoc cm (seq_of_matrix mx)) [SMTPat(foldm cm mx)]

(*| Builds the `m` by `n` matrix whose element at row `i` and column `j` is
    `generator i j`.

    The refined result type `FStar.Matrix.matrix_of` gives its elements. *)
val init : (#c:Type) -> (#m:pos) -> (#n: pos) -> (generator: matrix_generator c m n) 
  -> matrix_of generator 

(*| Proves that the fold of `init generator` is equivalent, under `eq`, to the
    fold over the rows of the fold of each row, both computed with
    `FStar.Seq.Permutation.foldm_snoc`.

    It also states the same for the fold of the flat sequence of the matrix. *)
val matrix_fold_equals_fold_of_seq_folds : (#c:Type) -> (#eq: CE.equiv c) -> 
                                           (#m: pos) -> (#n: pos) ->
                                           (cm: CE.cm c eq) ->
                                           (generator: matrix_generator c m n) ->
  Lemma (ensures foldm cm (init generator) `eq.eq`
         SP.foldm_snoc cm (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))))
         /\ SP.foldm_snoc cm (seq_of_matrix (init generator)) `eq.eq`
         SP.foldm_snoc cm (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))))         
         ) 

(* This auxiliary lemma shows that the fold of the last line of a matrix
   is equal to the corresponding fold of the generator function *)
 
(*| Proves that the fold of `init generator` is equivalent, under `eq`, to the
    nested `FStar.Algebra.CommMonoid.Fold.fold` over rows `0` to `m-1` and
    columns `0` to `n-1` of `generator`. *)
val matrix_fold_equals_func_double_fold  : (#c:Type) -> (#eq: CE.equiv c) -> 
                                           (#m: pos) -> (#n: pos) ->
                                           (cm: CE.cm c eq) ->
                                           (generator: matrix_generator c m n) ->
  Lemma (foldm cm (init generator) `eq.eq` 
           CF.fold cm 0 (m-1) (fun (i:under m) -> CF.fold cm 0 (n-1) (generator i)))
 
(*| Returns the generator of the transposed matrix: the result `f` satisfies
    `f j i == generator i j`.

    `FStar.Algebra.CommMonoid.Fold.Nested.transpose_generator` is the general
    version for arbitrary integer ranges. *)
val transposed_matrix_gen (#c:_) (#m:pos) (#n:pos) (generator: matrix_generator c m n) 
  : (f: matrix_generator c n m { forall i j. f j i == generator i j }) 

(*| Proves that the flat sequence of the transposed matrix is a permutation of
    that of the original matrix, via the index map `transpose_ji m n`.

    The permutation is in the sense of `FStar.Seq.Permutation.is_permutation`. *)
val matrix_transpose_is_permutation (#c:_) (#m #n: pos) 
                                    (generator: matrix_generator c m n)
  : Lemma (SP.is_permutation (seq_of_matrix (init generator))
                             (seq_of_matrix (init (transposed_matrix_gen generator)))
                             (transpose_ji m n))
                             
(*| Proves that folding a matrix and folding its transpose give equivalent
    results, under `eq`. *)
val matrix_fold_equals_fold_of_transpose (#c:_) (#eq:_)
                                         (#m #n: pos) 
                                         (cm: CE.cm c eq) 
                                         (gen: matrix_generator c m n)
  : Lemma (foldm cm (init gen) `eq.eq`
           foldm cm (init (transposed_matrix_gen gen)))

(*| Element-wise equivalence of `m` by `n` matrices, lifting the equivalence
    `eq` on elements to an `FStar.Algebra.CommMonoid.Equiv.equiv` on matrices.

    Two matrices are equivalent when all their corresponding elements are; see
    `FStar.Matrix.matrix_equiv_ijth` and `FStar.Matrix.matrix_equiv_from_element_eq`. *)
val matrix_equiv : (#c: Type) ->
                   (eq:  CE.equiv c) ->
                   (m: pos) -> (n: pos) ->
                   CE.equiv (matrix c m n)                   

(*| Proves that corresponding elements of equivalent matrices are equivalent
    under `eq`. *)
val matrix_equiv_ijth (#c:_) (#m #n: pos) (eq: CE.equiv c) 
                      (ma mb: matrix c m n) (i: under m) (j: under n)
  : Lemma (requires (matrix_equiv eq m n).eq ma mb) 
          (ensures ijth ma i j `eq.eq` ijth mb i j) 

(*| Proves that two matrices are equivalent from the equivalence of all their
    corresponding elements, stated as a quantified precondition. *)
val matrix_equiv_from_element_eq (#c:_) (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n)
  : Lemma (requires (forall (i: under m) (j: under n). ijth ma i j `eq.eq` ijth mb i j))
          (ensures (matrix_equiv eq m n).eq ma mb)

(* 
   Notice that even though we can (and will) construct CommMonoid for matrix addition,
   we still publish the operations as well since as soon as we get to multiplication,
   results usually have different dimensions, so it would be convenient to have both
   the CommMonoid for matrix addition and the explicit addition function.

   This becomes the only way with non-square matrix multiplication, since these 
   would not constitute a monoid to begin with.
*)

(*| Proves that two matrices are equivalent from a lemma that establishes the
    equivalence of their elements at any row `i` and column `j`.

    A variant of `FStar.Matrix.matrix_equiv_from_element_eq` that avoids
    calling `FStar.Classical.forall_intro_2` in the caller's proof, which can
    be costly in large proofs. *)
let matrix_equiv_from_proof #c (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n)
  (proof: (i:under m) -> (j:under n) -> Lemma (eq.eq (ijth ma i j) (ijth mb i j)))
  : Lemma ((matrix_equiv eq m n).eq ma mb)
  = Classical.forall_intro_2 proof; 
    matrix_equiv_from_element_eq eq ma mb 

(*| The generator of the sum of two matrices: the element at row `i` and column
    `j` is `add.mult (ijth ma i j) (ijth mb i j)`. *)
let matrix_add_generator #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n) 
  : matrix_generator c m n = fun i j -> add.mult (ijth ma i j) (ijth mb i j)

(*| The element-wise sum of two matrices of the same dimensions, using the
    operation of the commutative monoid `add`.

    `FStar.Matrix.matrix_add_comm_monoid` packages it as a commutative monoid. *)
let matrix_add #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n) 
  : matrix_of (matrix_add_generator add ma mb)
  = init (matrix_add_generator add ma mb)  

(*| Proves that the element at row `i` and column `j` of `matrix_add add ma mb`
    is `add.mult (ijth ma i j) (ijth mb i j)`. *)
let matrix_add_ijth #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n) (i: under m) (j: under n)
  : Lemma (ijth (matrix_add add ma mb) i j == add.mult (ijth ma i j) (ijth mb i j)) = ()

(*| The commutative monoid of `m` by `n` matrices under
    `FStar.Matrix.matrix_add`, up to `FStar.Matrix.matrix_equiv`.

    Its unit is the matrix whose elements are all `add.unit`. *)
val matrix_add_comm_monoid : (#c:Type) -> 
                             (#eq:CE.equiv c) -> 
                             (add: CE.cm c eq) -> 
                             (m:pos) -> (n: pos) -> 
                             CE.cm (matrix c m n) (matrix_equiv eq m n)


(*| Returns column `j` of a matrix as a sequence of length `m`.

    See `FStar.Matrix.matrix_row_col_lemma`. *)
let col #c #m #n (mx: matrix c m n) (j: under n) = SB.init m (fun (i: under m) -> ijth mx i j) 

(*| Returns row `i` of a matrix as a sequence of length `n`.

    See `FStar.Matrix.matrix_row_col_lemma`. *)
let row #c #m #n (mx: matrix c m n) (i: under m) = SB.init n (fun (j: under n) -> ijth mx i j) 

(*| Proves that `ijth mx i j` is element `j` of `row mx i` and element `i` of
    `col mx j`. *)
val matrix_row_col_lemma (#c:_) (#m #n:pos) (mx: matrix c m n) (i: under m) (j: under n) 
  : Lemma (ijth mx i j == SB.index (row mx i) j /\ ijth mx i j == SB.index (col mx j) i)  

(*| Multiplies every element of `s` on the right by `const`, using `cm.mult`.

    `FStar.Matrix.const_op_seq` multiplies on the left. *)
let seq_op_const #c #eq (cm: CE.cm c eq) (s: SB.seq c) (const: c) 
  = SB.init (SB.length s) (fun (i: under (SB.length s)) -> cm.mult (SB.index s i) const)

(*| Multiplies every element of `s` on the left by `const`, using `cm.mult`.

    By commutativity this is equivalent to `FStar.Matrix.seq_op_const`, but
    only up to `eq`; the two are kept separate so that proofs can use
    propositional equality `==` where it holds. *)
let const_op_seq #c #eq (cm: CE.cm c eq) (const: c) (s: SB.seq c)                       
  = SB.init (SB.length s) (fun (i: under (SB.length s)) -> cm.mult const (SB.index s i))


(*| The element-wise product of two sequences of the same length, using
    `mul.mult`. *)
let seq_of_products #c #eq (mul: CE.cm c eq) (s: SB.seq c) (t: SB.seq c {SB.length t == SB.length s})
  = SB.init (SB.length s) (fun (i: under (SB.length s)) -> SB.index s i `mul.mult` SB.index t i)

(*| Proves that `seq_of_products mul s t` equals any sequence `r` that is
    extensionally equal (`FStar.Seq.Base.equal`) to the element-wise product.

    Cheaper in large proofs than calling `FStar.Seq.Base.lemma_eq_elim`. *)
val seq_of_products_lemma (#c:_) (#eq:_) (mul: CE.cm c eq) 
                          (s: SB.seq c) (t: SB.seq c {SB.length t == SB.length s})
                          (r: SB.seq c { SB.equal r (SB.init (SB.length s) 
                                                             (fun (i: under (SB.length s)) -> 
                                                                    SB.index s i `mul.mult` SB.index t i))})
  : Lemma (seq_of_products mul s t == r)  

(*| The dot product of two sequences of the same length: the `add`-fold of
    their element-wise `mul`-products. *)
let dot #c #eq (add mul: CE.cm c eq) (s: SB.seq c) (t: SB.seq c{SB.length t == SB.length s}) 
  = SP.foldm_snoc add (seq_of_products mul s t) 

(*| Proves that `dot add mul s t` is `FStar.Seq.Permutation.foldm_snoc` of
    `seq_of_products mul s t`, its definition. *)
val dot_lemma (#c:_) (#eq:_) (add mul: CE.cm c eq) (s: SB.seq c) (t: SB.seq c{SB.length t == SB.length s}) 
  : Lemma (dot add mul s t == SP.foldm_snoc add (seq_of_products mul s t)) 

(* Of course, it would be best to define the matrix product as a convolution,
   but we don't have all the necessary framework for that level of generality yet. *)
(*| The product of an `m` by `n` matrix and an `n` by `p` matrix, given an
    addition monoid `add` and a multiplication monoid `mul` on the elements.

    The element at row `i` and column `k` is the dot product
    `FStar.Matrix.dot add mul (row mx i) (col my k)`; see
    `FStar.Matrix.matrix_mul_ijth`. Most algebraic lemmas about it require
    `FStar.Matrix.is_fully_distributive mul add` and
    `FStar.Matrix.is_absorber add.unit mul`. *)
val matrix_mul (#c:_) (#eq:_) (#m #n #p:pos) (add mul: CE.cm c eq) (mx: matrix c m n) (my: matrix c n p)  
  : matrix c m p

(*| States that `mul` distributes over `add` on the left, up to `eq`:
    `mul.mult x (add.mult y z)` is equivalent to
    `add.mult (mul.mult x y) (mul.mult x z)`. *)
let is_left_distributive #c #eq (mul add: CE.cm c eq) = 
  forall (x y z: c). mul.mult x (add.mult y z) `eq.eq` add.mult (mul.mult x y) (mul.mult x z)

(*| States that `mul` distributes over `add` on the right, up to `eq`:
    `mul.mult (add.mult x y) z` is equivalent to
    `add.mult (mul.mult x z) (mul.mult y z)`. *)
let is_right_distributive #c #eq (mul add: CE.cm c eq) = 
  forall (x y z: c). mul.mult (add.mult x y) z `eq.eq` add.mult (mul.mult x z) (mul.mult y z)

(*| States that `mul` distributes over `add` on both sides; see
    `FStar.Matrix.is_left_distributive` and `FStar.Matrix.is_right_distributive`. *)
let is_fully_distributive #c #eq (mul add: CE.cm c eq) = is_left_distributive mul add /\ is_right_distributive mul add

(* 
   This definition is of course far more general than matrices, and should rather 
   be a part of algebra core, as it is relevant to any magma. 
   
   In the process of development of F* abstract algebra framework, this definition
   will probably take its rightful place near the most basic of grouplike structures.

   Also note that this property is defined via forall. We would probably want
   to make such properties opaque to SMT in the future, to avoid verification performance
   issues.
*)
(*| States that `z` is absorbing for the operation of `op`, up to `eq`:
    `op.mult z x` and `op.mult x z` are equivalent to `z` for all `x`.

    Typically used with the unit of addition and the multiplication monoid,
    where zero annihilates. *)
let is_absorber #c #eq (z:c) (op: CE.cm c eq) = 
  forall (x:c). op.mult z x `eq.eq` z /\ op.mult x z `eq.eq` z

(* 
   Similar lemmas to reason about matrix product elements 
   We're going to refactor these a bit, as some are clearly redundant.
   Might want to keep internal usages to one variant of the lemma and
   remove the rest.
*)
(*| Proves that the element at row `i` and column `h` of the product is the dot
    product of row `i` of `mx` and column `h` of `my`. *)
val matrix_mul_ijth (#c:_) (#eq:_) (#m #n #k:pos) (add mul: CE.cm c eq) 
                    (mx: matrix c m n) (my: matrix c n k) (i: under m) (h: under k)
  : Lemma (ijth (matrix_mul add mul mx my) i h == dot add mul (row mx i) (col my h))

(*| Proves that the element at row `i` and column `k` of the product is the
    `add`-fold of `mul.mult (ijth mx i j) (ijth my j k)` over `j`. *)
val matrix_mul_ijth_as_sum (#c:_) (#eq:_) (#m #n #p:pos) (add mul: CE.cm c eq)  
                    (mx: matrix c m n) (my: matrix c n p) (i: under m) (k: under p) 
  : Lemma (ijth (matrix_mul add mul mx my) i k == 
           SP.foldm_snoc add (SB.init n (fun (j: under n) -> mul.mult (ijth mx i j) (ijth my j k))))  

(*| Proves that the element at row `i` and column `k` of the product is the
    `add`-fold of any sequence `r` extensionally equal to the products of
    row `i` of `mx` and column `k` of `my`. *)
val matrix_mul_ijth_eq_sum_of_seq (#c:_) (#eq:_) (#m #n #p:pos) (add: CE.cm c eq) 
                                  (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                                  (mx: matrix c m n) (my: matrix c n p) (i: under m) (k: under p)
                                  (r: SB.seq c{r `SB.equal` seq_of_products mul (row mx i) (col my k)})
  : Lemma (ijth (matrix_mul add mul mx my) i k == SP.foldm_snoc add r) 
  
(*| Proves that the element at row `i` and column `k` of the product is the
    `add`-fold of `FStar.Seq.Base.init n f`, for any `f` that generates the products of
    row `i` of `mx` and column `k` of `my`. *)
val matrix_mul_ijth_eq_sum_of_seq_for_init (#c:_) (#eq:_) (#m #n #p:pos) (add mul: CE.cm c eq)  
    (mx: matrix c m n) (my: matrix c n p) (i: under m) (k: under p) 
    (f: under n -> c { SB.init n f `SB.equal` seq_of_products mul (row mx i) (col my k)})
  : Lemma (ijth (matrix_mul add mul mx my) i k == SP.foldm_snoc add (SB.init n f))


(*| Proves that matrix multiplication is associative up to
    `FStar.Matrix.matrix_equiv`: writing `*` for `matrix_mul add mul`,
    `(mx * my) * mz` is equivalent to `mx * (my * mz)`.

    Requires `mul` to distribute over `add` and `add.unit` to be absorbing for
    `mul`. *)
val matrix_mul_is_associative (#c:_) (#eq:_) (#m #n #p #q: pos) (add: CE.cm c eq) 
  (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
  (mx: matrix c m n) (my: matrix c n p) (mz: matrix c p q)
  : Lemma ((matrix_equiv eq m q).eq ((matrix_mul add mul mx my) `matrix_mul add mul` mz)
                            (matrix_mul add mul mx (matrix_mul add mul my mz)))

(*| The `m` by `m` identity matrix: `mul.unit` on the diagonal and `add.unit`
    elsewhere.

    See `FStar.Matrix.matrix_mul_identity`. *)
let matrix_mul_unit #c #eq (add mul: CE.cm c eq) m
  : matrix c m m = init (fun i j -> if i=j then mul.unit else add.unit)

(*| Proves that multiplying a square matrix on the right by
    `FStar.Matrix.matrix_mul_unit` gives an equivalent matrix.

    Requires `add.unit` to be absorbing for `mul`. *)
val matrix_mul_right_identity (#c:_) (#eq:_) (#m: pos) (add: CE.cm c eq) 
                              (mul: CE.cm c eq{is_absorber add.unit mul}) 
                              (mx: matrix c m m)
  : Lemma (matrix_mul add mul mx (matrix_mul_unit add mul m) `(matrix_equiv eq m m).eq` mx)
  
(*| Proves that multiplying a square matrix on the left by
    `FStar.Matrix.matrix_mul_unit` gives an equivalent matrix.

    Requires `add.unit` to be absorbing for `mul`. *)
val matrix_mul_left_identity (#c:_) (#eq:_) (#m: pos) (add: CE.cm c eq) 
                             (mul: CE.cm c eq{is_absorber add.unit mul}) 
                             (mx: matrix c m m)
  : Lemma (matrix_mul add mul (matrix_mul_unit add mul m) mx `(matrix_equiv eq m m).eq` mx)
  
(*| Proves that `FStar.Matrix.matrix_mul_unit` is a two-sided identity for
    matrix multiplication, up to `FStar.Matrix.matrix_equiv`.

    The conjunction of `FStar.Matrix.matrix_mul_left_identity` and
    `FStar.Matrix.matrix_mul_right_identity`. *)
val matrix_mul_identity (#c:_) (#eq:_) (#m: pos) (add: CE.cm c eq) 
                        (mul: CE.cm c eq{is_absorber add.unit mul}) 
                        (mx: matrix c m m)
  : Lemma (matrix_mul add mul mx (matrix_mul_unit add mul m) `(matrix_equiv eq m m).eq` mx /\
           matrix_mul add mul (matrix_mul_unit add mul m) mx `(matrix_equiv eq m m).eq` mx)

(*| Proves that matrix multiplication respects `FStar.Matrix.matrix_equiv`:
    equivalent factors give equivalent products. *)
val matrix_mul_congruence (#c:_) (#eq:_) (#m #n #p:pos) (add mul: CE.cm c eq)  
                          (mx: matrix c m n) (my: matrix c n p) 
                          (mz: matrix c m n) (mw: matrix c n p)
  : Lemma (requires (matrix_equiv eq m n).eq mx mz /\ (matrix_equiv eq n p).eq my mw)
          (ensures (matrix_equiv eq m p).eq (matrix_mul add mul mx my) 
                                            (matrix_mul add mul mz mw))

(*| Proves that matrix multiplication distributes over matrix addition on the
    left, up to `FStar.Matrix.matrix_equiv`: writing `*` for `matrix_mul add mul`
    and `+` for `matrix_add add`, `mx * (my + mz)` is equivalent to `mx * my + mx * mz`.

    Requires `mul` to distribute over `add` and `add.unit` to be absorbing for
    `mul`. *)
val matrix_mul_is_left_distributive (#c:_) (#eq:_) (#m #n #p:pos) (add: CE.cm c eq)
                                    (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                                    (mx: matrix c m n) (my mz: matrix c n p)
  : Lemma (matrix_mul add mul mx (matrix_add add my mz) `(matrix_equiv eq m p).eq`
           matrix_add add (matrix_mul add mul mx my) (matrix_mul add mul mx mz))
            
(*| Proves that matrix multiplication distributes over matrix addition on the
    right, up to `FStar.Matrix.matrix_equiv`: writing `*` for `matrix_mul add mul`
    and `+` for `matrix_add add`, `(mx + my) * mz` is equivalent to `mx * mz + my * mz`.

    Requires `mul` to distribute over `add` and `add.unit` to be absorbing for
    `mul`. *)
val matrix_mul_is_right_distributive (#c:_) (#eq:_) (#m #n #p:pos) (add: CE.cm c eq)
                                    (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                                    (mx my: matrix c m n) (mz: matrix c n p)
  : Lemma (matrix_mul add mul (matrix_add add mx my) mz `(matrix_equiv eq m p).eq`
           matrix_add add (matrix_mul add mul mx mz) (matrix_mul add mul my mz))
