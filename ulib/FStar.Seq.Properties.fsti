(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module FStar.Seq.Properties

open FStar.Seq.Base
module Seq = FStar.Seq.Base

(*| The type of sequences of elements of type `a` whose length is exactly `l`. *)
let lseq (a: Type) (l: nat) : Tot Type =
    s: Seq.seq a { Seq.length s == l }

(*| Holds when `j` is a valid index of `s`, that is `0 <= j` and `j < length s`. *)
let indexable (#a:Type) (s:Seq.seq a) (j:int) = 0 <= j /\ j < Seq.length s

(*| If `append s1 s2` equals `append t1 t2` and `length s1 = length t1`, then
    `s1` and `t1` have the same element at every index `i < length s1`.

    See `FStar.Seq.Properties.lemma_append_inj` for the whole-sequence version. *)
val lemma_append_inj_l: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a{length s1 = length t1 /\ equal (append s1 s2) (append t1 t2)} -> i:nat{i < length s1}
  -> Lemma (index s1 i == index t1 i)

(*| If `append s1 s2` equals `append t1 t2` and the corresponding parts have the
    same lengths, then `s2` and `t2` have the same element at every index
    `i < length s2`. *)
val lemma_append_inj_r: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a{length s1 = length t1 /\ length s2 = length t2 /\ equal (append s1 s2) (append t1 t2)} -> i:nat{i < length s2}
  -> Lemma (ensures  (index s2 i == index t2 i))

(*| If `append s1 s2` equals `append t1 t2` and either the first parts or the
    second parts have the same length, then both pairs have the same length. *)
val lemma_append_len_disj: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a {(length s1 = length t1 \/ length s2 = length t2) /\ (equal (append s1 s2) (append t1 t2))}
  -> Lemma (ensures (length s1 = length t1 /\ length s2 = length t2))

(*| Concatenation is injective when the lengths match: if `append s1 s2` equals
    `append t1 t2` and `length s1 = length t1` or `length s2 = length t2`, then
    `s1` equals `t1` and `s2` equals `t2` (in the sense of `FStar.Seq.Base.equal`). *)
val lemma_append_inj: #a:Type -> s1:seq a -> s2:seq a -> t1:seq a -> t2:seq a {length s1 = length t1 \/ length s2 = length t2}
  -> Lemma (requires (equal (append s1 s2) (append t1 t2)))
           (ensures (equal s1 t1 /\ equal s2 t2))

(*| Returns the first element of a non-empty sequence.

    See also `FStar.Seq.Properties.tail` and `FStar.Seq.Properties.last`. *)
let head (#a:Type) (s:seq a{length s > 0}) : Tot a = index s 0

(*| Returns a non-empty sequence without its first element, as
    `slice s 1 (length s)`.

    See also `FStar.Seq.Properties.head`. *)
let tail (#a:Type) (s:seq a{length s > 0}) : Tot (seq a) = slice s 1 (length s)

(*| The head of `append s1 s2` is the head of `s1`, when `s1` is non-empty. *)
val lemma_head_append: #a:Type -> s1:seq a{length s1 > 0} -> s2:seq a -> Lemma
  (head (append s1 s2) == head s1)

(*| The tail of `append s1 s2` is `append (tail s1) s2`, when `s1` is non-empty. *)
val lemma_tail_append: #a:Type -> s1:seq a{length s1 > 0} -> s2:seq a -> Lemma
  (tail (append s1 s2) == append (tail s1) s2)

(*| Returns the last element of a non-empty sequence, at index `length s - 1`.

    See also `FStar.Seq.Properties.un_snoc`. *)
let last (#a:Type) (s:seq a{length s > 0}) : Tot a = index s (length s - 1)

(*| `FStar.Seq.Base.cons` is injective: if `cons v1 s1` equals `cons v2 s2`
    (in the sense of `FStar.Seq.Base.equal`), then `v1 == v2` and `s1` equals
    `s2`. *)
val lemma_cons_inj: #a:Type -> v1:a -> v2:a -> s1:seq a -> s2:seq a
  -> Lemma (requires (equal (cons v1 s1) (cons v2 s2)))
          (ensures (v1 == v2 /\ equal s1 s2))

(*| Splits a sequence at index `i` into the prefix `slice s 0 i` and the suffix
    `slice s i (length s)`.

    `FStar.Seq.Properties.lemma_split` shows that appending the two parts gives
    back `s`; `FStar.Seq.Properties.split_eq` returns the split with that fact. *)
let split (#a:Type) (s:seq a) (i:nat{(0 <= i /\ i <= length s)}) : Tot (seq a & seq a)
  = slice s 0 i, slice s i (length s)

(*| Appending the two parts of `FStar.Seq.Properties.split s i` gives back `s`. *)
val lemma_split : #a:Type -> s:seq a -> i:nat{(0 <= i /\ i <= length s)} -> Lemma
  (ensures (append (fst (split s i)) (snd (split s i)) == s))

(*| `FStar.Seq.Properties.split` with a postcondition stating that appending the
    two parts gives back `s`. *)
let split_eq (#a:Type) (s:seq a) (i:nat{(0 <= i /\ i <= length s)})
: Pure
  (seq a & seq a)
  (requires True)
  (ensures (fun x -> (append (fst x) (snd x) == s)))
= let x = split s i in
  lemma_split s i;
  x

(*| Returns the number of occurrences of `x` in `s`, using decidable equality.

    See `FStar.Seq.Properties.mem` and `FStar.Seq.Properties.permutation`. *)
let rec count (#a:eqtype) (x:a) (s:seq a) : Tot nat (decreases (length s))
= if length s = 0 then 0
  else if head s = x
  then 1 + count x (tail s)
  else count x (tail s)

(*| Decides whether `x` occurs in `s`, defined as `count x s > 0`.

    For element types without decidable equality, use the propositional
    `FStar.Seq.Properties.contains`. *)
let mem (#a:eqtype) (x:a) (l:seq a) : Tot bool = count x l > 0

(*| If `x` is a member of `s`, then some index of `s` holds `x`.

    `FStar.Seq.Properties.index_mem` computes the first such index. *)
val mem_index (#a:eqtype) (x:a) (s:seq a)
    : Lemma (requires (mem x s))
            (ensures (exists i. index s i == x))

(*| Returns the first index of `x` in `s`, given that `mem x s` holds.

    The result `i` satisfies `i < length s` and `index s i == x`. *)
let rec index_mem (#a:eqtype) (x:a) (s:seq a)
    : Pure nat
           (requires (mem x s))
           (ensures (fun i -> i < length s /\ index s i == x))
           (decreases (length s))
    = if head s = x then 0
      else 1 + index_mem x (tail s)

(*| Returns `s` with the elements at indices `i` and `j` exchanged. When `i = j`
    the sequence is unchanged.

    `FStar.Seq.Properties.lemma_swap_permutes` shows that the result is a
    permutation of `s`. *)
let swap (#a:Type) (s:seq a) (i:nat{i<length s}) (j:nat{j<length s}) : Tot (seq a)
= upd (upd s j (index s i)) i (index s j)

(*| Splits off the first element of `s1` in a concatenation: `append s1 s2`
    equals `append (slice s1 0 1) (append (slice s1 1 (length s1)) s2)`, for
    non-empty `s1`. *)
val lemma_slice_append: #a:Type -> s1:seq a{length s1 >= 1} -> s2:seq a -> Lemma
  (ensures (equal (append s1 s2) (append (slice s1 0 1) (append (slice s1 1 (length s1)) s2))))

(*| Dropping the first `i` elements of `append s1 s2`, with `i <= length s1`,
    gives `append (slice s1 i (length s1)) s2`. *)
val lemma_slice_first_in_append: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i <= length s1} -> Lemma
  (ensures (equal (slice (append s1 s2) i (length (append s1 s2))) (append (slice s1 i (length s1)) s2)))

(*| Updating an index outside `[i, j)` does not change `slice s i j`: when
    `k < i` or `j <= k`, `slice (upd s k v) i j == slice s i j`.

    Triggered automatically on `slice (upd s k v) i j`. *)
val slice_upd: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s}
  -> k:nat{k < length s} -> v:a -> Lemma
  (requires k < i \/ j <= k)
  (ensures  slice (upd s k v) i j == slice s i j)
  [SMTPat (slice (upd s k v) i j)]

(*| Updating index `k` of `slice s i j` is the same as updating index `i + k` of
    `s` and then slicing: `upd (slice s i j) k v == slice (upd s (i + k) v) i j`.

    Triggered automatically on `upd (slice s i j) k v`. *)
val upd_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s}
  -> k:nat{k < j - i} -> v:a -> Lemma
  (requires i + k < j)
  (ensures  upd (slice s i j) k v == slice (upd s (i + k) v) i j)
  [SMTPat (upd (slice s i j) k v)]

// TODO: should be renamed cons_head_append, or something like that (because it is NOT related to (append (cons _ _) _))
(*| For non-empty `s1`, `append s1 s2` equals
    `cons (head s1) (append (tail s1) s2)`.

    Despite its name, this is not about `append (cons x s1) s2`; for that see
    `FStar.Seq.Properties.append_cons`. *)
val lemma_append_cons: #a:Type -> s1:seq a{length s1 > 0} -> s2:seq a -> Lemma
  (requires True)
  (ensures (equal (append s1 s2) (cons (head s1) (append (tail s1) s2))))

(*| The tail of `cons hd tl` equals `tl`. *)
val lemma_tl: #a:Type -> hd:a -> tl:seq a -> Lemma
  (ensures (equal (tail (cons hd tl)) tl))

(*| Decides whether every pair of adjacent elements of `s` is related by `f`.

    When `f` is a total order (`FStar.Seq.Properties.total_order`), this means
    that `f` holds between any two elements in index order; see
    `FStar.Seq.Sorted.sorted_sorted_pred_lemma`. Sequences of length 0 or 1 are
    sorted. *)
let rec sorted (#a:Type) (f:a -> a -> Tot bool) (s:seq a)
: Tot bool (decreases (length s))
= if length s <= 1
  then true
  else let hd = head s in
       f hd (index s 1) && sorted f (tail s)

(*| `FStar.Seq.Properties.sorted` gives the same answer for two comparison
    functions that agree on all arguments. *)
val sorted_feq (#a:Type)
               (f g : (a -> a -> Tot bool))
               (s:seq a{forall x y. f x y == g x y})
   : Lemma (ensures (sorted f s <==> sorted g s))


(*| For every `x`, `count x (append lo hi)` is `count x lo + count x hi`.

    `FStar.Seq.Properties.lemma_append_count_aux` states it for one `x`. *)
val lemma_append_count: #a:eqtype -> lo:seq a -> hi:seq a -> Lemma
  (requires True)
  (ensures (forall x. count x (append lo hi) = (count x lo + count x hi)))

(*| `count x (append lo hi)` is `count x lo + count x hi`, for a given `x`. *)
val lemma_append_count_aux: #a:eqtype -> x:a -> lo:seq a -> hi:seq a -> Lemma
  (requires True)
  (ensures (count x (append lo hi) = (count x lo + count x hi)))

(*| In a non-empty sequence, `x` is a member exactly when it is the head or a
    member of the tail. *)
val lemma_mem_inversion: #a:eqtype -> s:seq a{length s > 0} -> Lemma
  (ensures (forall x. mem x s = (x=head s || mem x (tail s))))

(*| If the predicate `f` holds for the element at every index of `s`, then it
    holds for every member of `s`. *)
val lemma_mem_count: #a:eqtype -> s:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (forall (i:nat{i<length s}). f (index s i)))
  (ensures (forall (x:a). mem x s ==> f x))

(*| Splitting `s` at index `i` splits the counts: for every `x`, `count x s` is
    the sum of the counts of `x` in `slice s 0 i` and `slice s i (length s)`. *)
val lemma_count_slice: #a:eqtype -> s:seq a -> i:nat{i<=length s} -> Lemma
  (requires True)
  (ensures (forall x. count x s = count x (slice s 0 i) + count x (slice s i (length s))))

(*| Holds when the boolean relation `f` is a total order (like `<=`): reflexive,
    transitive, and such that for distinct `a1` and `a2` exactly one of
    `f a1 a2` and `f a2 a1` holds.

    `FStar.Seq.Properties.tot_ord` is the type of such relations. *)
type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
(*| The type of boolean relations on `a` that are total orders in the sense of
    `FStar.Seq.Properties.total_order`. *)
type tot_ord (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

(*| Combines sorted sequences around a pivot: if `lo` and `hi` are sorted by the
    total order `f`, every member of `lo` is `f`-below `pivot`, and `pivot` is
    `f`-below every member of `hi`, then `append lo (cons pivot hi)` is sorted.

    This is the combination step of quicksort. *)
val sorted_concat_lemma: #a:eqtype
                      -> f:(a -> a -> Tot bool){total_order a f}
                      -> lo:seq a{sorted f lo}
                      -> pivot:a
                      -> hi:seq a{sorted f hi}
                      -> Lemma (requires (forall y. (mem y lo ==> f y pivot)
                                                 /\ (mem y hi ==> f pivot y)))
                               (ensures (sorted f (append lo (cons pivot hi))))

(*| Splits `s` around two indices `i < j` into five pieces: `slice s 0 i`, the
    element at `i`, `slice s (i+1) j`, the element at `j`, and
    `slice s (j+1) (length s)`.

    The postcondition states each piece and that their concatenation equals `s`. *)
val split_5 : #a:Type -> s:seq a -> i:nat -> j:nat{i < j && j < length s} -> Pure (seq (seq a))
  (requires True)
  (ensures (fun x ->
            (length x = 5
             /\ equal s (append (index x 0) (append (index x 1) (append (index x 2) (append (index x 3) (index x 4)))))
             /\ equal (index x 0) (slice s 0 i)
             /\ equal (index x 1) (slice s i (i+1))
             /\ equal (index x 2) (slice s (i+1) j)
             /\ equal (index x 3) (slice s j (j + 1))
             /\ equal (index x 4) (slice s (j + 1) (length s)))))

(*| Describes `swap s i j` piecewise: a slice `[i', j')` lying entirely below
    `i`, entirely above `j`, or strictly between `i` and `j` is unchanged, and the
    one-element slices at `i` and `j` are exchanged.

    Used to prove `FStar.Seq.Properties.lemma_swap_permutes`. *)
val lemma_swap_permutes_aux_frag_eq: #a:Type -> s:seq a -> i:nat{i<length s} -> j:nat{i <= j && j<length s}
                          -> i':nat -> j':nat{i' <= j' /\ j'<=length s /\
                                              (j < i'  //high slice
                                              \/ j' <= i //low slice
                                              \/ (i < i' /\ j' <= j)) //mid slice
                                              }
                          -> Lemma (ensures (slice s i' j' == slice (swap s i j) i' j'
                                            /\ slice s i (i + 1) == slice (swap s i j) j (j + 1)
                                            /\ slice s j (j + 1) == slice (swap s i j) i (i + 1)))

(*| `FStar.Seq.Properties.swap` does not change the number of occurrences of `x`.

    `FStar.Seq.Properties.lemma_swap_permutes` states it for all elements. *)
val lemma_swap_permutes_aux: #a:eqtype -> s:seq a -> i:nat{i<length s} -> j:nat{i <= j && j<length s} -> x:a -> Lemma
  (requires True)
  (ensures (count x s = count x (swap s i j)))

(*| Holds when `s1` and `s2` contain every element the same number of times, as
    measured by `FStar.Seq.Properties.count`.

    Permutations have the same length (`FStar.Seq.Properties.perm_len`).
    `FStar.Seq.Permutation.seqperm` is a different notion that carries an
    explicit index bijection; `FStar.Seq.Permutation.permutation_from_equal_counts`
    builds one from this property. *)
type permutation (a:eqtype) (s1:seq a) (s2:seq a) =
       (forall i. count i s1 = count i s2)

(*| Concatenation preserves permutations: if `s1'` permutes `s1` and `s2'`
    permutes `s2`, then `append s1' s2'` permutes `append s1 s2`. *)
val append_permutations: #a:eqtype -> s1:seq a -> s2:seq a -> s1':seq a -> s2':seq a -> Lemma
    (requires permutation a s1 s1' /\ permutation a s2 s2')
    (ensures permutation a (append s1 s2) (append s1' s2'))

(*| `swap s i j` is a permutation of `s`.

    ```fstar
    let swap_ends (s: FStar.Seq.Base.seq int{FStar.Seq.Base.length s > 0})
      : Lemma (FStar.Seq.Properties.permutation int s
                 (FStar.Seq.Properties.swap s 0 (FStar.Seq.Base.length s - 1)))
      = FStar.Seq.Properties.lemma_swap_permutes s 0 (FStar.Seq.Base.length s - 1)
    ``` *)
val lemma_swap_permutes (#a:eqtype) (s:seq a) (i:nat{i<length s}) (j:nat{i <= j && j<length s})
  : Lemma (permutation a s (swap s i j))

(*| Sequences that are permutations of each other have the same length. *)
val perm_len (#a:eqtype) (s1 s2: seq a)
  : Lemma (requires (permutation a s1 s2))
          (ensures  (length s1 == length s2))

(*| If `tl` is a permutation of `tail s`, then `cons (head s) tl` is a
    permutation of `s`. *)
val cons_perm: #a:eqtype -> tl:seq a -> s:seq a{length s > 0} ->
         Lemma (requires (permutation a tl (tail s)))
               (ensures (permutation a (cons (head s) tl) s))

(*| `x` is a member of `append s1 s2` exactly when it is a member of `s1` or of
    `s2`, for every `x`. *)
val lemma_mem_append : #a:eqtype -> s1:seq a -> s2:seq a
      -> Lemma (ensures (forall x. mem x (append s1 s2) <==> (mem x s1 || mem x s2)))

(*| `x` is a member of `slice s i j` (with `i < j`) exactly when it is the
    element at `i` or a member of `slice s (i + 1) j`. *)
val lemma_slice_cons: #a:eqtype -> s:seq a -> i:nat -> j:nat{i < j && j <= length s}
  -> Lemma (ensures (forall x. mem x (slice s i j) <==> (x = index s i || mem x (slice s (i + 1) j))))

(*| `x` is a member of `slice s i j` (with `i < j`) exactly when it is the
    element at `j - 1` or a member of `slice s i (j - 1)`. *)
val lemma_slice_snoc: #a:eqtype -> s:seq a -> i:nat -> j:nat{i < j && j <= length s}
  -> Lemma (ensures (forall x. mem x (slice s i j) <==> (x = index s (j - 1) || mem x (slice s i (j - 1)))))

(*| Extends a bound upward by one index: if every member of `slice s i j` is
    `f`-below `pv` and so is `index s j`, then every member of
    `slice s i (j + 1)` is `f`-below `pv`. *)
val lemma_ordering_lo_snoc: #a:eqtype -> f:tot_ord a -> s:seq a -> i:nat -> j:nat{i <= j && j < length s} -> pv:a
   -> Lemma (requires ((forall y. mem y (slice s i j) ==> f y pv) /\ f (index s j) pv))
            (ensures ((forall y. mem y (slice s i (j + 1)) ==> f y pv)))

(*| Extends a bound downward by one index: if `pv` is `f`-below every member of
    `slice s (back + 1) len` and below `index s back`, then it is `f`-below every
    member of `slice s back len`. *)
val lemma_ordering_hi_cons: #a:eqtype -> f:tot_ord a -> s:seq a -> back:nat -> len:nat{back < len && len <= length s} -> pv:a
   -> Lemma (requires ((forall y. mem y (slice s (back + 1) len) ==> f pv y) /\ f pv (index s back)))
            (ensures ((forall y. mem y (slice s back len) ==> f pv y)))

(*| `swap s i j` leaves `slice s lo i` unchanged, for `lo <= i <= j`. *)
val swap_frame_lo : #a:Type -> s:seq a -> lo:nat -> i:nat{lo <= i} -> j:nat{i <= j && j < length s}
     -> Lemma (ensures (slice s lo i == slice (swap s i j) lo i))

(*| `swap s i j` leaves `slice s lo i'` unchanged, for `lo <= i' <= i <= j`. *)
val swap_frame_lo' : #a:Type -> s:seq a -> lo:nat -> i':nat {lo <= i'} -> i:nat{i' <= i} -> j:nat{i <= j && j < length s}
     -> Lemma (ensures (slice s lo i' == slice (swap s i j) lo i'))

(*| `swap s i j` leaves `slice s k hi` unchanged, for `i <= j < k <= hi`. *)
val swap_frame_hi : #a:Type -> s:seq a -> i:nat -> j:nat{i <= j} -> k:nat{j < k} -> hi:nat{k <= hi /\ hi <= length s}
     -> Lemma (ensures (slice s k hi == slice (swap s i j) k hi))

(*| Swapping commutes with slicing: when `start <= i <= j < len`, slicing
    `swap s i j` to `[start, len)` gives the slice of `s` with the elements at
    offsets `i - start` and `j - start` swapped. *)
val lemma_swap_slice_commute  : #a:Type -> s:seq a -> start:nat -> i:nat{start <= i} -> j:nat{i <= j} -> len:nat{j < len && len <= length s}
    -> Lemma (ensures (slice (swap s i j) start len == (swap (slice s start len) (i - start) (j - start))))

(*| When `start <= i <= j < len`, the slice `[start, len)` of `swap s i j` is a
    permutation of the same slice of `s`. *)
val lemma_swap_permutes_slice : #a:eqtype -> s:seq a -> start:nat -> i:nat{start <= i} -> j:nat{i <= j} -> len:nat{j < len && len <= length s}
   -> Lemma (ensures (permutation a (slice s start len) (slice (swap s i j) start len)))

(*| Returns `s1` with the elements in `[i, j)` replaced by those of `s2` at the
    same indices. The sequences must have the same length.

    `s1 == splice s2 i s1 j` expresses that `s1` and `s2` agree outside
    `[i, j)`; the frame lemmas of this module use it that way. *)
let splice (#a:Type) (s1:seq a) (i:nat) (s2:seq a{length s1=length s2}) (j:nat{i <= j /\ j <= (length s2)})
: Tot (seq a)
= Seq.append (slice s1 0 i) (Seq.append (slice s2 i j) (slice s1 j (length s1)))

(*| Returns `s` with the elements in `[i, j)` replaced by `sub`, which has length
    `j - i`. *)
let replace_subseq (#a:Type0) (s:Seq.seq a) (i:nat) (j:nat{i <= j /\ j <= length s}) (sub:Seq.seq a{length sub == j - i}) :Tot (Seq.seq a)
  = Seq.append (Seq.slice s 0 i) (Seq.append sub (Seq.slice s j (Seq.length s)))

(*| Splicing a sequence with itself gives the same sequence. *)
val splice_refl : #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s}
  -> Lemma
  (ensures (s == splice s i s j))

(*| `swap s i j` agrees with `s` outside `[start, len)`, for
    `start <= i <= j < len`, stated as
    `swap s i j == splice s start (swap s i j) len`. *)
val lemma_swap_splice : #a:Type -> s:seq a -> start:nat -> i:nat{start <= i} -> j:nat{i <= j} -> len:nat{j < len && len <= length s}
   -> Lemma
        (ensures (swap s i j == splice s start (swap s i j) len))

(*| If `s1` and `s2` agree outside `[i, j)` (stated as
    `s1 == splice s2 i s1 j`), then they agree on `slice s1 m n` and at index
    `m`, for `j <= m < n`. *)
val lemma_seq_frame_hi: #a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat{i <= j} -> m:nat{j <= m} -> n:nat{m < n && n <= length s1}
  -> Lemma
  (requires (s1 == (splice s2 i s1 j)))
  (ensures  ((slice s1 m n == slice s2 m n) /\ (index s1 m == index s2 m)))

(*| If `s1` and `s2` agree outside `[m, n)` (stated as
    `s1 == splice s2 m s1 n`), then they agree on `slice s1 i j` and at index
    `j`, for `j < m`. *)
val lemma_seq_frame_lo: #a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat{i <= j} -> m:nat{j < m} -> n:nat{m <= n && n <= length s1}
  -> Lemma
  (requires (s1 == (splice s2 m s1 n)))
  (ensures  ((slice s1 i j == slice s2 i j) /\ (index s1 j == index s2 j)))

(*| The tail of `slice s i j` (with `i < j`) is `slice s (i + 1) j`.

    Triggered automatically on `tail (slice s i j)`. *)
val lemma_tail_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i < j && j <= length s}
  -> Lemma
  (requires True)
  (ensures (tail (slice s i j) == slice s (i + 1) j))
  [SMTPat (tail (slice s i j))]

(*| If `s1` and `s2` agree outside `[i, j)`, they agree outside `[i, k)` for
    `j <= k`. Agreement is stated with `FStar.Seq.Properties.splice`. *)
val lemma_weaken_frame_right : #a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j && j <= k && k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 i s1 j))
  (ensures (s1 == splice s2 i s1 k))

(*| If `s1` and `s2` agree outside `[j, k)`, they agree outside `[i, k)` for
    `i <= j`. Agreement is stated with `FStar.Seq.Properties.splice`. *)
val lemma_weaken_frame_left : #a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j && j <= k && k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 j s1 k))
  (ensures (s1 == splice s2 i s1 k))

(*| Agreement outside `[i, j)` is transitive: if `s1` agrees with `s2` and `s2`
    with `s3` outside `[i, j)`, then `s1` agrees with `s3` there. *)
val lemma_trans_frame : #a:Type -> s1:seq a -> s2:seq a -> s3:seq a{length s1 = length s2 /\ length s2 = length s3} -> i:nat -> j:nat{i <= j && j <= length s1}
  -> Lemma
  (requires ((s1 == splice s2 i s1 j) /\ s2 == splice s3 i s2 j))
  (ensures (s1 == splice s3 i s1 j))

(*| Widens a permuted range to the left: if `s1` agrees with `s2` outside
    `[j, k)` and the slices `[j, k)` are permutations of each other, then the
    slices `[i, k)` are permutations of each other, for `i <= j`. *)
val lemma_weaken_perm_left: #a:eqtype -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j /\ j <= k /\ k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 j s1 k /\ permutation a (slice s2 j k) (slice s1 j k)))
  (ensures (permutation a (slice s2 i k) (slice s1 i k)))

(*| Widens a permuted range to the right: if `s1` agrees with `s2` outside
    `[i, j)` and the slices `[i, j)` are permutations of each other, then the
    slices `[i, k)` are permutations of each other, for `j <= k`. *)
val lemma_weaken_perm_right: #a:eqtype -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j /\ j <= k /\ k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 i s1 j /\ permutation a (slice s2 i j) (slice s1 i j)))
  (ensures (permutation a (slice s2 i k) (slice s1 i k)))

(*| Permutation of the slices `[i, j)` is transitive across three sequences. *)
val lemma_trans_perm: #a:eqtype -> s1:seq a -> s2:seq a -> s3:seq a{length s1 = length s2 /\ length s2 = length s3} -> i:nat -> j:nat{i<=j && j <= length s1}
 -> Lemma
  (requires (permutation a (slice s1 i j) (slice s2 i j)
             /\ permutation a (slice s2 i j) (slice s3 i j)))
  (ensures (permutation a (slice s1 i j) (slice s3 i j)))


(*New additions, please review*)

(*| Returns `s` with `x` added at the end.

    `FStar.Seq.Properties.un_snoc` is its inverse. *)
let snoc (#a:Type) (s:seq a) (x:a) : Tot (seq a) = Seq.append s (Seq.create 1 x)

(*| Adding at both ends commutes: `cons hd (snoc s tl)` equals
    `snoc (cons hd s) tl`. *)
val lemma_cons_snoc (#a:Type) (hd:a) (s:Seq.seq a) (tl:a)
  : Lemma (requires True)
          (ensures (Seq.equal (cons hd (snoc s tl))
                              (snoc (cons hd s) tl)))

(*| For non-empty `s`, `tail (snoc s x) == snoc (tail s) x`. *)
val lemma_tail_snoc: #a:Type -> s:Seq.seq a{Seq.length s > 0} -> x:a
                     -> Lemma (ensures (tail (snoc s x) == snoc (tail s) x))

(*| `FStar.Seq.Properties.snoc` is injective: if `snoc s1 v1` equals
    `snoc s2 v2`, then `v1 == v2` and `s1` equals `s2`. *)
val lemma_snoc_inj: #a:Type -> s1:seq a -> s2:seq a -> v1:a -> v2:a
  -> Lemma (requires (equal (snoc s1 v1) (snoc s2 v2)))
          (ensures (v1 == v2 /\ equal s1 s2))

(*| `y` is a member of `snoc s x` exactly when it is a member of `s` or equal to
    `x`. *)
val lemma_mem_snoc : #a:eqtype -> s:Seq.seq a -> x:a ->
   Lemma (ensures (forall y. mem y (snoc s x) <==> mem y s \/ x=y))

(*| Returns the first element of `l`, from the left, that satisfies `f`, or
    `None` if there is none.

    `FStar.Seq.Properties.find_r` searches from the right and
    `FStar.Seq.Properties.ghost_find_l` takes a ghost predicate. *)
let rec find_l (#a:Type) (f:a -> Tot bool) (l:seq a)
: Tot (o:option a{Some? o ==> f (Some?.v o)})
  (decreases (Seq.length l))
= if Seq.length l = 0 then None
  else if f (head l) then Some (head l)
  else find_l f (tail l)

(*| `FStar.Seq.Properties.find_l` for a ghost predicate `f`; the result is ghost. *)
let rec ghost_find_l (#a:Type) (f:a -> GTot bool) (l:seq a)
: GTot (o:option a{Some? o ==> f (Some?.v o)})
  (decreases (Seq.length l))
= if Seq.length l = 0 then None
  else if f (head l) then Some (head l)
  else ghost_find_l f (tail l)

(*| If `find_l f s1` finds an element, then `find_l f (append s1 s2)` finds the
    same one. *)
val find_append_some: #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (Some? (find_l f s1)))
  (ensures (find_l f (append s1 s2) == find_l f s1))

(*| If `find_l f s1` is `None`, then `find_l f (append s1 s2)` is
    `find_l f s2`. *)
val find_append_none: #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (None? (find_l f s1)))
  (ensures (find_l f (append s1 s2) == find_l f s2))

(*| If `find_l f s2` is `None`, then `find_l f (append s1 s2)` is
    `find_l f s1`. *)
val find_append_none_s2: #a:Type -> s1:seq a -> s2:seq a -> f:(a -> Tot bool) -> Lemma
  (requires (None? (find_l f s2)))
  (ensures  (find_l f (append s1 s2) == find_l f s1))

(*| Relates `find_l f (snoc s x)` to `find_l f s`: when it is `None`, so is
    `find_l f s` and `f x` is false; when it is `Some y`, the result equals
    `find_l f s` or else `y` is `x` and `f x` holds. *)
val find_snoc: #a:Type -> s:Seq.seq a -> x:a -> f:(a -> Tot bool)
               -> Lemma (ensures (let res = find_l f (snoc s x) in
                                 match res with
                                 | None -> find_l f s == None /\ not (f x)
                                 | Some y -> res == find_l f s \/ (f x /\ x==y)))

(*| Splits a non-empty sequence into its prefix and its last element.

    The result `(prefix, x)` satisfies `s == snoc prefix x`. *)
let un_snoc (#a:Type) (s:seq a{length s <> 0}) : Tot (r:(seq a & a){s == snoc (fst r) (snd r)}) =
  let s', a = split s (length s - 1) in
  assert (Seq.equal (snoc s' (Seq.index a 0)) s);
  s', Seq.index a 0

(*| `un_snoc (snoc s x)` is `(s, x)`. *)
val un_snoc_snoc (#a:Type) (s:seq a) (x:a) : Lemma (un_snoc (snoc s x) == (s, x))

(*| Returns the last element of `l` that satisfies `f`, searching from the right,
    or `None` if there is none.

    See also `FStar.Seq.Properties.find_l`. *)
let rec find_r (#a:Type) (f:a -> Tot bool) (l:seq a)
: Tot (o:option a{Some? o ==> f (Some?.v o)})
  (decreases (Seq.length l))
= if Seq.length l = 0 then None
  else let prefix, last = un_snoc l in
       if f last then Some last
       else find_r f prefix

(*| A trivially true predicate on indices, used as an SMT pattern trigger for the
    witness index in the postcondition of `FStar.Seq.Properties.seq_find`. *)
type found (i:nat) = True

(*| Helper for `FStar.Seq.Properties.seq_find`: searches the indices below `ctr`,
    from `ctr - 1` downward, given that no index at or above `ctr` satisfies `f`. *)
let rec seq_find_aux (#a:Type) (f:a -> Tot bool) (l:seq a) (ctr:nat{ctr <= Seq.length l})
: Pure (option a)
  (requires (forall (i:nat{ i < Seq.length l /\ i >= ctr}).
               not (f (Seq.index l i) )))
  (ensures (function
            | None -> forall (i:nat{i < Seq.length l}).  not (f (Seq.index l i))
            | Some x -> f x /\  (exists (i:nat{i < Seq.length l}). {:pattern (found i)}
                                 found i /\ x == Seq.index l i)))
= match ctr with
  | 0 -> None
  | _ -> let i = ctr - 1 in
  if f (Seq.index l i)
  then (
     cut (found i);
     Some (Seq.index l i))
  else seq_find_aux f l i

(*| Searches `l` for an element satisfying `f`.

    `None` means that no element satisfies `f`. `Some x` means that `f x` holds
    and that `x` is at some index `i` of `l`; the existential is guarded by the
    pattern `found i` (see `FStar.Seq.Properties.found`). The specification does
    not say which matching element is returned; the implementation scans from the
    end and returns the last one. *)
let seq_find (#a:Type) (f:a -> Tot bool) (l:seq a)
: Pure (option a)
  (requires True)
  (ensures (function
            | None -> forall (i:nat{i < Seq.length l}). not (f (Seq.index l i))
            | Some x -> f x /\ (exists (i:nat{i < Seq.length l}).{:pattern (found i)}
                                 found i /\ x == Seq.index l i)))
= seq_find_aux f l (Seq.length l)

(*| If `x` is a member of `s` and satisfies `f`, then
    `FStar.Seq.Properties.seq_find f s` returns some element satisfying `f`. *)
val find_mem (#a:eqtype) (s:seq a) (f:a -> Tot bool) (x:a{f x})
   : Lemma (requires (mem x s))
           (ensures (Some? (seq_find f s) /\ f (Some?.v (seq_find f s))))

(*| Decides whether `f` holds for every element of `l`. The postcondition states
    that the result is `true` exactly when `f (index l i)` holds for every index
    `i`. *)
let for_all
  (#a: Type)
  (f: (a -> Tot bool))
  (l: seq a)
: Pure bool
  (requires True)
  (ensures (fun b -> (b == true <==> (forall (i: nat {i < Seq.length l} ) . f (index l i) == true))))
= None? (seq_find (fun i -> not (f i)) l)

(*| The element at any index of `s` is a member of `s`.

    Triggered automatically on `mem (index s n) s`. *)
val seq_mem_k: #a:eqtype -> s:seq a -> n:nat{n < Seq.length s} ->
    Lemma (requires True)
          (ensures (mem (Seq.index s n) s))
          [SMTPat (mem (Seq.index s n) s)]

module L = FStar.List.Tot

(*| Unfolds `seq_of_list l` one step: it is `empty` for the empty list, and for
    `hd :: tl` it is `cons hd (seq_of_list tl)`, with head `hd` and tail
    `seq_of_list tl`. *)
val lemma_seq_of_list_induction (#a:Type) (l:list a)
  :Lemma (requires True)
         (ensures (let s = seq_of_list l in
                   match l with
                   | []    -> Seq.equal s empty
                   | hd::tl -> s == cons hd (seq_of_list tl) /\
		             head s == hd /\ tail s == (seq_of_list tl)))

(*| Converting a sequence to a list and back gives the original sequence.

    The same fact as `FStar.Seq.Base.lemma_seq_of_seq_to_list`, which has an SMT
    pattern. *)
val lemma_seq_list_bij: #a:Type -> s:seq a -> Lemma
  (requires (True))
  (ensures  (seq_of_list (seq_to_list s) == s))

(*| Converting a list to a sequence and back gives the original list.

    The same fact as `FStar.Seq.Base.lemma_seq_to_seq_of_list`, which has an SMT
    pattern. *)
val lemma_list_seq_bij: #a:Type -> l:list a -> Lemma
  (requires (True))
  (ensures  (seq_to_list (seq_of_list l) == l))

(*| The postcondition of `FStar.Seq.Properties.createL`: `s` has the length of
    `l`, and `l` and `s` convert to each other with `seq_to_list` and
    `seq_of_list`.

    The length equation is wrapped in `normalize`, so that the length of a
    literal list is computed during typechecking. *)
unfold let createL_post (#a:Type0) (l:list a) (s:seq a) : prop =
  normalize (L.length l = length s) /\ seq_to_list s == l /\ seq_of_list l == s

(*| Builds a sequence from a list, typically a literal list.

    The result is `seq_of_list l`. Its postcondition,
    `FStar.Seq.Properties.createL_post`, gives the length directly, which makes
    it convenient for constants.

    ```fstar
    let abc : FStar.Seq.Base.seq int = FStar.Seq.Properties.createL [1; 2; 3]

    let _ = assert (FStar.Seq.Base.length abc == 3)
    ``` *)
let createL (#a:Type0) (l:list a)
: Pure (seq a)
  (requires True)
  (ensures (fun s -> createL_post #a l s))
= let s = seq_of_list l in
  lemma_list_seq_bij l;
  s
  
(*| The element at index `i` of `s` is the element at index `i` of
    `seq_to_list s`. *)
val lemma_index_is_nth: #a:Type -> s:seq a -> i:nat{i < length s} -> Lemma
  (requires True)
  (ensures  (L.index (seq_to_list s) i == index s i))

////////////////////////////////////////////////////////////////////////////////
//s `contains` x : Type0
//    An undecidable version of `mem`,
//    for when the sequence payload is not an eqtype
////////////////////////////////////////////////////////////////////////////////
(*| Holds when `x` occurs at some index of `s`.

    A propositional version of `FStar.Seq.Properties.mem` that does not require
    decidable equality. The definition is hidden: introduce and eliminate it with
    `FStar.Seq.Properties.contains_intro` and
    `FStar.Seq.Properties.contains_elim`. *)
[@@ remove_unused_type_parameters [0; 1; 2]]
val contains (#a:Type) (s:seq a) (x:a) : Tot prop

(*| If `k < length s` and `index s k == x`, then `s` contains `x`. *)
val contains_intro (#a:Type) (s:seq a) (k:nat) (x:a)
  : Lemma (k < Seq.length s /\ Seq.index s k == x
            ==>
           s `contains` x)

(*| If `s` contains `x`, then `x` is at some index `k < length s`. *)
val contains_elim (#a:Type) (s:seq a) (x:a)
  : Lemma (s `contains` x
            ==>
          (exists (k:nat). k < Seq.length s /\ Seq.index s k == x))

(*| The empty sequence contains no element. *)
val lemma_contains_empty (#a:Type) : Lemma (forall (x:a). ~ (contains Seq.empty x))

(*| The only element contained in `create 1 x` is `x`. *)
val lemma_contains_singleton (#a:Type) (x:a) : Lemma (forall (y:a). contains (create 1 x) y ==> y == x)

(*| `append s1 s2` contains `x` exactly when `s1` or `s2` contains `x`. *)
val append_contains_equiv (#a:Type) (s1:seq a) (s2:seq a) (x:a)
  : Lemma ((append s1 s2) `contains` x
            <==>
           (s1 `contains` x \/ s2 `contains` x))

(*| `snoc s x` contains `y` exactly when `s` contains `y` or `x == y`. *)
val contains_snoc : #a:Type -> s:Seq.seq a -> x:a ->
   Lemma (ensures (forall y. (snoc s x) `contains` y  <==> s `contains` y \/ x==y))

(*| The element found by `FStar.Seq.Properties.find_l`, if any, is contained in
    the sequence. *)
val lemma_find_l_contains (#a:Type) (f:a -> Tot bool) (l:seq a)
  : Lemma (requires True) (ensures Some? (find_l f l) ==> l `contains` (Some?.v (find_l f l)))

(*| `cons hd tl` contains `x` exactly when `x == hd` or `tl` contains `x`. *)
val contains_cons (#a:Type) (hd:a) (tl:Seq.seq a) (x:a)
  : Lemma ((cons hd tl) `contains` x
           <==>
           (x==hd \/ tl `contains` x))

(*| Moves an element across a concatenation: `append u (cons x v)` equals
    `append (snoc u x) v`. *)
val append_cons_snoc (#a:Type) (u: Seq.seq a) (x:a) (v:Seq.seq a)
    : Lemma (Seq.equal (Seq.append u (cons x v))
                       (Seq.append (snoc u x) v))

(*| Recovers the parts of a concatenation by slicing: `s1` equals the slice
    `[0, length s1)` of `append s1 s2`, `s2` equals the slice starting at
    `length s1`, and each slice `[i, j)` of `s2` equals the slice
    `[length s1 + i, length s1 + j)` of the concatenation. *)
val append_slices (#a:Type) (s1:Seq.seq a) (s2:Seq.seq a)
   : Lemma ( Seq.equal s1 (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1)) /\
             Seq.equal s2 (Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2)) /\
             (forall (i:nat) (j:nat).
                i <= j /\ j <= Seq.length s2 ==>
                Seq.equal (Seq.slice s2 i j)
                          (Seq.slice (Seq.append s1 s2) (Seq.length s1 + i) (Seq.length s1 + j))))


(*| If `find_l f s` is `None`, then `f` is false for the element at every index
    of `s`. *)
val find_l_none_no_index (#a:Type) (s:Seq.seq a) (f:(a -> Tot bool)) :
  Lemma (requires (None? (find_l f s)))
        (ensures (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i))))
        (decreases (Seq.length s))

(** More properties, with new naming conventions *)

(*| Holds when `s_suff` is a suffix of `s`: `s == append s_pref s_suff` for some
    `s_pref`. *)
let suffix_of
  (#a: Type)
  (s_suff s: seq a)
= exists s_pref . (s == append s_pref s_suff)

(*| A non-empty sequence is the `cons` of its head and its tail.

    Triggered automatically on `cons (head s) (tail s)`. *)
val cons_head_tail
  (#a: Type)
  (s: seq a {length s > 0})
: Lemma
  (requires True)
  (ensures (s == cons (head s) (tail s)))
  [SMTPat (cons (head s) (tail s))]

(*| The head of `cons x s` is `x`. *)
val head_cons
  (#a: Type)
  (x: a)
  (s: seq a)
: Lemma
  (ensures (head (cons x s) == x))

(*| The tail of a non-empty sequence is a suffix of it.

    Triggered automatically on `suffix_of (tail s) s`. *)
val suffix_of_tail
  (#a: Type)
  (s: seq a {length s > 0})
: Lemma
  (requires True)
  (ensures ((tail s) `suffix_of` s))
  [SMTPat ((tail s) `suffix_of` s)]

(*| The element at index 0 of `cons c s` is `c`. *)
val index_cons_l
  (#a: Type)
  (c: a)
  (s: seq a)
: Lemma
  (ensures (index (cons c s) 0 == c))

(*| The element at index `i` of `cons c s`, for `1 <= i <= length s`, is the
    element at index `i - 1` of `s`. *)
val index_cons_r
  (#a: Type)
  (c: a)
  (s: seq a)
  (i: nat {1 <= i /\ i <= length s})
: Lemma
  (ensures (index (cons c s) i == index s (i - 1)))

(*| `append (cons c s1) s2 == cons c (append s1 s2)`. *)
val append_cons
  (#a: Type)
  (c: a)
  (s1 s2: seq a)
: Lemma
  (ensures (append (cons c s1) s2 == cons c (append s1 s2)))

(*| The element at index `i` of `tail s` is the element at index `i + 1` of `s`. *)
val index_tail
  (#a: Type)
  (s: seq a {length s > 0})
  (i: nat {i < length s - 1} )
: Lemma
  (ensures (index (tail s) i == index s (i + 1)))

(*| `y` is a member of `cons x s` exactly when it is a member of `s` or equal to
    `x`. *)
val mem_cons
  (#a:eqtype)
  (x:a)
  (s:seq a)
: Lemma
  (ensures (forall y. mem y (cons x s) <==> mem y s \/ x=y))

(*| Extends a slice by one element at the end: for `i <= j < length s`,
    `snoc (slice s i j) (index s j) == slice s i (j + 1)`.

    Triggered automatically on `snoc (slice s i j) (index s j)`. *)
val snoc_slice_index
  (#a: Type)
  (s: seq a)
  (i: nat)
  (j: nat {i <= j /\ j < length s} )
: Lemma
  (requires True)
  (ensures (snoc (slice s i j) (index s j) == slice s i (j + 1)))
  [SMTPat (snoc (slice s i j) (index s j))]

(*| Extends a slice by one element at the front: for `i < j <= length s`,
    `cons (index s i) (slice s (i + 1) j) == slice s i j`.

    The index `i + 1` is passed as the separate argument `k` so that the lemma
    can be triggered automatically on `cons (index s i) (slice s k j)`. *)
val cons_index_slice
  (#a: Type)
  (s: seq a)
  (i: nat)
  (j: nat {i < j /\ j <= length s} )
  (k:nat{k == i+1})
: Lemma
  (requires True)
  (ensures (cons (index s i) (slice s k j) == slice s i j))
  [SMTPat (cons (index s i) (slice s k j))]

(*| The slice `[i, i)` of any sequence is `FStar.Seq.Base.empty`.

    Triggered automatically on `slice s i i`. *)
val slice_is_empty
  (#a: Type)
  (s: seq a)
  (i: nat {i <= length s})
: Lemma
  (requires True)
  (ensures (slice s i i == Seq.empty))
  [SMTPat (slice s i i)]

(*| The slice `[0, length s)` of `s` is `s` itself.

    Triggered automatically on `slice s 0 (length s)`. *)
val slice_length
  (#a: Type)
  (s: seq a)
: Lemma
  (requires True)
  (ensures (slice s 0 (length s) == s))
  [SMTPat (slice s 0 (length s))]

(*| A slice of a slice is a slice of the original sequence:
    `slice (slice s i1 j1) i2 j2 == slice s (i1 + i2) (i1 + j2)`.

    Triggered automatically on `slice (slice s i1 j1) i2 j2`. *)
val slice_slice
  (#a: Type)
  (s: seq a)
  (i1: nat)
  (j1: nat {i1 <= j1 /\ j1 <= length s} )
  (i2: nat)
  (j2: nat {i2 <= j2 /\ j2 <= j1 - i1} )
: Lemma
  (requires True)
  (ensures (slice (slice s i1 j1) i2 j2 == slice s (i1 + i2) (i1 + j2)))
  [SMTPat (slice (slice s i1 j1) i2 j2)]

(*| The element at index `i` of `seq_of_list l` is the element at index `i` of
    `l`.

    Triggered automatically on `index (seq_of_list l) i`. *)
val lemma_seq_of_list_index (#a:Type) (l:list a) (i:nat{i < List.Tot.length l})
  :Lemma (requires True)
         (ensures  (index (seq_of_list l) i == List.Tot.index l i))
         [SMTPat (index (seq_of_list l) i)]

(*| Deprecated: the same as `FStar.Seq.Base.seq_of_list`. Use that instead. *)
[@@(deprecated "seq_of_list")]
let of_list (#a:Type) (l:list a) :seq a = seq_of_list l

(*| For a non-empty list, `seq_of_list (FStar.List.Tot.Base.tl l)` is the tail of
    `seq_of_list l`. *)
val seq_of_list_tl
  (#a: Type)
  (l: list a { List.Tot.length l > 0 } )
: Lemma
  (requires True)
  (ensures (seq_of_list (List.Tot.tl l) == tail (seq_of_list l)))

(*| `x` is a member of `seq_of_list l` exactly when it is a member of `l`
    (`FStar.List.Tot.Base.mem`).

    Triggered automatically on `mem x (seq_of_list l)`. *)
val mem_seq_of_list
  (#a: eqtype)
  (x: a)
  (l: list a)
: Lemma
  (requires True)
  (ensures (mem x (seq_of_list l) == List.Tot.mem x l))
  [SMTPat (mem x (seq_of_list l))]

(** Dealing efficiently with `seq_of_list` by meta-evaluating conjunctions over
an entire list. *)

(*| The conjunction stating that the elements of `s` from index `i` on are the
    elements of `l`: `index s (i + k) == FStar.List.Tot.Base.index l k` for every `k`.

    Used through `FStar.Seq.Properties.pointwise_and`. *)
let rec explode_and (#a: Type)
  (i: nat)
  (s: seq a { i <= length s })
  (l: list a { List.Tot.length l + i = length s }):
  Tot prop
  (decreases (List.Tot.length l))
= match l with
  | [] -> True
  | hd :: tl -> index s i == hd /\ explode_and (i + 1) s tl

(*| States that `s` has the elements of the list `l`, as an explicit conjunction
    of index equations computed by normalization.

    For a literal list this unfolds to `index s 0 == x0 /\ index s 1 == x1 /\ ...`.
    `FStar.Seq.Properties.intro_of_list` and
    `FStar.Seq.Properties.elim_of_list` convert between this form and
    `s == seq_of_list l`. *)
unfold
let pointwise_and s l =
  norm [ iota; zeta; primops; delta_only [ `%(explode_and) ] ] (explode_and 0 s l)

(*| If `FStar.Seq.Properties.explode_and i s l` holds, then `seq_of_list l`
    equals the slice of `s` starting at `i`.

    Used to prove `FStar.Seq.Properties.intro_of_list`. *)
val intro_of_list': #a:Type ->
  i:nat ->
  s:seq a ->
  l:list a ->
  Lemma
    (requires (
      List.Tot.length l + i = length s /\
      i <= length s /\
      explode_and i s l))
    (ensures (
      equal (seq_of_list l) (slice s i (length s))))

(*| Proves `s == seq_of_list l` from the element-wise equations
    `FStar.Seq.Properties.pointwise_and s l`, when `l` and `s` have the same
    length. *)
val intro_of_list (#a: Type) (s: seq a) (l: list a):
  Lemma
    (requires (
      List.Tot.length l = length s /\
      pointwise_and s l))
    (ensures (
      s == seq_of_list l))

(*| If the slice of `s` starting at `i` is `seq_of_list l`, then
    `FStar.Seq.Properties.explode_and i s l` holds.

    Used to prove `FStar.Seq.Properties.elim_of_list`. *)
val elim_of_list': #a:Type ->
  i:nat ->
  s:seq a ->
  l:list a ->
  Lemma
    (requires (
      List.Tot.length l + i = length s /\
      i <= length s /\
      slice s i (length s) == seq_of_list l))
    (ensures (
      explode_and i s l))

(*| Gives the element-wise equations `FStar.Seq.Properties.pointwise_and` for
    `seq_of_list l`. *)
val elim_of_list (#a: Type) (l: list a):
  Lemma
    (ensures (
      let s = seq_of_list l in
      pointwise_and s l))

(****** sortWith ******)
(*| Sorts `s` using the comparison function `f`, which returns a negative number
    when its first argument comes first.

    Implemented with `FStar.List.Tot.Base.sortWith`.
    `FStar.Seq.Properties.lemma_seq_sortwith_correctness` states that the result
    is a sorted permutation; `FStar.Seq.Properties.sort_lseq` packages this for a
    total order. *)
let sortWith (#a:eqtype) (f:a -> a -> Tot int) (s:seq a) :Tot (seq a)
  = seq_of_list (List.Tot.Base.sortWith f (seq_to_list s))

(*| Every element occurs as many times in `s` as in `seq_to_list s`. *)
val lemma_seq_to_list_permutation (#a:eqtype) (s:seq a)
  :Lemma (requires True) (ensures (forall x. count x s == List.Tot.Base.count x (seq_to_list s))) (decreases (length s))

(*| Every element occurs as many times in `l` as in `seq_of_list l`. *)
val lemma_seq_of_list_permutation (#a:eqtype) (l:list a)
  :Lemma (forall x. List.Tot.Base.count x l == count x (seq_of_list l))

(*| If the list `l` is sorted by `f` (`FStar.List.Tot.Properties.sorted`), then
    `seq_of_list l` is sorted by `f`. *)
val lemma_seq_of_list_sorted (#a:Type) (f:a -> a -> Tot bool) (l:list a)
  :Lemma (requires (List.Tot.Properties.sorted f l)) (ensures  (sorted f (seq_of_list l)))

(*| `sortWith f s` is sorted by `FStar.List.Tot.Base.bool_of_compare f` and is a
    permutation of `s`, provided `bool_of_compare f` is a total order in the
    sense of `FStar.Seq.Properties.total_order`. *)
val lemma_seq_sortwith_correctness (#a:eqtype) (f:a -> a -> Tot int) (s:seq a)
  :Lemma (requires (total_order a (List.Tot.Base.bool_of_compare f)))
         (ensures  (let s' = sortWith f s in sorted (List.Tot.Base.bool_of_compare f) s' /\ permutation a s s'))

(*| Sorts a sequence by the total order `f`. The result has the same length,
    is sorted by `f`, and is a permutation of the input.

    Wraps `FStar.Seq.Properties.sortWith`.

    ```fstar
    let sort_ints (#n: nat) (s: FStar.Seq.Properties.lseq int n)
      : FStar.Seq.Properties.lseq int n
      = FStar.Seq.Properties.sort_lseq (fun x y -> x <= y) s
    ``` *)
let sort_lseq (#a:eqtype) #n (f:tot_ord a) (s:lseq a n)
  : s':lseq a n{sorted f s' /\ permutation a s s'} =
  lemma_seq_sortwith_correctness (L.compare_of_bool f) s;
  let s' = sortWith (L.compare_of_bool f) s in
  perm_len s s';
  sorted_feq f (L.bool_of_compare (L.compare_of_bool f)) s';
  s'

(*| Folds `f` over `s` from the right: the result is
    `f s0 (f s1 (... (f sn init)))`, where `s0` is the first element.

    See also `FStar.Seq.Properties.foldr_snoc`. *)
let rec foldr (#a #b:Type) (f:b -> a -> Tot a) (s:seq b) (init:a)
  : Tot a (decreases (length s))
  = if length s = 0 then init
    else f (head s) (foldr f (tail s) init)

(*| Folds `f` over `s` by removing the last element first: the result is
    `f sn (... (f s1 (f s0 init)))`, where `sn` is the last element.

    This is the order of a left fold with the arguments of `f` flipped.
    `FStar.Seq.Permutation.foldm_snoc` is defined with it. *)
let rec foldr_snoc (#a #b:Type) (f:b -> a -> Tot a) (s:seq b) (init:a)
  : Tot a (decreases (length s))
  = if length s = 0 then init
    else let s, last = un_snoc s in
         f last (foldr_snoc f s init)

(****** Seq map ******)

(*| Applies `f` to every element of a sequence.

    `FStar.Seq.Properties.map_seq_len` and `FStar.Seq.Properties.map_seq_index`
    state its length and elements. *)
val map_seq (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a) : Tot (Seq.seq b)

(*| `map_seq f s` has the same length as `s`. *)
val map_seq_len (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a)
  : Lemma (ensures Seq.length (map_seq f s) == Seq.length s)

(*| The element at index `i` of `map_seq f s` is `f (index s i)`. *)
val map_seq_index (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a) (i:nat{i < Seq.length s})
  : Lemma (ensures (map_seq_len f s; Seq.index (map_seq f s) i == f (Seq.index s i)))

(*| `map_seq` distributes over concatenation. *)
val map_seq_append (#a #b:Type) (f:a -> Tot b) (s1 s2:Seq.seq a)
  : Lemma (ensures (map_seq f (Seq.append s1 s2) ==
                    Seq.append (map_seq f s1) (map_seq f s2)))
