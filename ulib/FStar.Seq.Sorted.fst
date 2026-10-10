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
module FStar.Seq.Sorted

open FStar.Seq

(*| Holds when `f` relates every two elements of `s` in index order: for all
    indices `i <= j`, `f (index s i) (index s j)`.

    For a total order this is equivalent to the boolean
    `FStar.Seq.Properties.sorted`; see `FStar.Seq.Sorted.sorted_pred_sorted_lemma`
    and `FStar.Seq.Sorted.sorted_sorted_pred_lemma`. *)
let sorted_pred (#a:eqtype) (f:tot_ord a) (s:seq a) : prop =
  forall (i j: (k:nat{k<length s})). i <= j ==> f (index s i) (index s j)

(*| The tail of a sequence satisfying `FStar.Seq.Sorted.sorted_pred` also
    satisfies it. *)
val sorted_pred_tail :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a{length s > 0} ->
  Lemma (requires (sorted_pred #a f s)) (ensures (sorted_pred #a f (tail s)))
let sorted_pred_tail #a f s = ()

(*| `FStar.Seq.Sorted.sorted_pred f s` implies `FStar.Seq.Properties.sorted f s`. *)
val sorted_pred_sorted_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a ->
  Lemma (requires (sorted_pred f s)) (ensures (sorted #a f s == true)) (decreases (length s))
let rec sorted_pred_sorted_lemma #a f s =
  if length s <= 1 then ()
  else begin
    assert (f (index s 0) (index s 1)) ;
    sorted_pred_tail #a f s;
    sorted_pred_sorted_lemma #a f (tail s)
  end

(*| Proves `FStar.Seq.Sorted.sorted_pred f s` from a lemma `g` establishing
    `f (index s i) (index s j)` for every `i <= j`. *)
let intro_sorted_pred (#a:eqtype) (f:tot_ord a) (s:seq a)
  ($g:(i:nat{i < length s} -> j:nat{j < length s} -> Lemma (requires (i <= j)) (ensures (f (index s i) (index s j)))))
  : Lemma (sorted_pred #a f s)
= let aux (i j : (k:nat{k < length s})) (p:squash (i <= j)) : GTot (squash (f (index s i) (index s j))) =
    g i j in
  FStar.Classical.forall_intro_2 (fun (i j:(k:nat{k < length s})) ->
    (FStar.Classical.arrow_to_impl (aux i j)) <: Lemma (i <= j ==> f (index s i) (index s j)))

(*| If the first two elements of `s` are related by `f` and the tail satisfies
    `FStar.Seq.Sorted.sorted_pred`, then `s` satisfies it. *)
val sorted_pred_cons_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a{length s > 1} ->
  Lemma (requires (f (index s 0) (index s 1) /\ sorted_pred #a f (tail s))) (ensures (sorted_pred #a f s))
let sorted_pred_cons_lemma #a f s =
  let aux (i j : (k:nat{k < length s})) : Lemma (requires (i <= j)) (ensures (f (index s i) (index s j))) =
    if i = 0 then
      if j = 0 then ()
      else assert (f (index s 0) (index (tail s) 0) /\ f (index (tail s) 0) (index (tail s) (j-1)))
    else assert (f (index (tail s) (i - 1)) (index (tail s) (j - 1)))
  in
  intro_sorted_pred #a f s aux

(*| For a total order `f`, `FStar.Seq.Properties.sorted f s` implies
    `FStar.Seq.Sorted.sorted_pred f s`, which relates all pairs of elements and
    not just adjacent ones.

    ```fstar
    let int_le (x y: int) : bool = x <= y

    let sorted_first_le_last (s: FStar.Seq.Base.seq int{FStar.Seq.Base.length s > 0})
      : Lemma (requires FStar.Seq.Properties.sorted int_le s)
              (ensures int_le (FStar.Seq.Base.index s 0) (FStar.Seq.Properties.last s))
      = FStar.Seq.Sorted.sorted_sorted_pred_lemma int_le s
    ``` *)
val sorted_sorted_pred_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a ->
  Lemma (requires (sorted #a f s == true)) (ensures (sorted_pred #a f s)) (decreases (length s))
let rec sorted_sorted_pred_lemma #a f s =
  if length s = 0 then ()
  else if length s = 1 then ()
  else (sorted_sorted_pred_lemma #a f (tail s) ; sorted_pred_cons_lemma #a f s)

(*| Every slice of a sequence satisfying `FStar.Seq.Sorted.sorted_pred` also
    satisfies it. *)
val sorted_pred_slice_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a ->
  i:nat{i < length s} ->
  j:nat{i <= j /\ j <= length s} ->
  Lemma (requires (sorted_pred #a f s)) (ensures (sorted_pred #a f (slice s i j)))
let sorted_pred_slice_lemma #a f s i j = ()

(*| Every slice of a sequence sorted by a total order is sorted. *)
val sorted_slice_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a ->
  i:nat{i < length s} ->
  j:nat{i <= j /\ j <= length s} ->
  Lemma (requires (sorted #a f s == true)) (ensures (sorted #a f (slice s i j) == true))
let sorted_slice_lemma #a f s i j =
  sorted_sorted_pred_lemma #a f s ;
  sorted_pred_slice_lemma #a f s i j ;
  sorted_pred_sorted_lemma #a f (slice s i j)

(*| Both parts of `FStar.Seq.Properties.split s i` are sorted when `s` is sorted
    by a total order. *)
val sorted_split_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s:seq a ->
  i:nat{i < length s} ->
  Lemma (requires (sorted #a f s == true))
    (ensures (let s1, s2 = split s i in sorted #a f s1 == true /\ sorted #a f s2 == true))
let sorted_split_lemma #a f s i =
  sorted_slice_lemma #a f s 0 i ;
  sorted_slice_lemma #a f s i (length s)

(*| Concatenation preserves `FStar.Seq.Sorted.sorted_pred` when the last element
    of `s1` is related by `f` to the first element of `s2` (if both are
    non-empty). *)
val sorted_pred_append_lemma :
  #a:eqtype ->
  f:tot_ord a ->
  s1:seq a ->
  s2:seq a ->
  Lemma (requires (sorted_pred #a f s1 /\ sorted_pred #a f s2 /\ (length s1 > 0 /\ length s2 > 0 ==> f (last s1) (head s2))))
    (ensures (sorted_pred #a f (append s1 s2)))
let sorted_pred_append_lemma #a f s1 s2 =
  let s = append s1 s2 in
  let aux (i j:(k:nat{k < length s})) : Lemma (requires (i <= j)) (ensures (f (index s i) (index s j))) =
    if i < length s1 then
      if j < length s1 then
        assert (f (index s1 i) (index s1 j))
      else
        (assert (f (index s1 i) (last s1)) ; assert (f (head s2) (index s2 (j - length s1))))
    else
      (assert (j >= length s1) ; assert (f (index s2 (i - length s1)) (index s2 (j - length s1))))
  in
  intro_sorted_pred #a f s aux
