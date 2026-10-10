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
module FStar.List.Pure.Properties

open FStar.List.Tot.Base
open FStar.List.Pure.Base
open FStar.List.Tot.Properties

(** Properties of splitAt *)

(*| Gives the lengths of the two parts of `FStar.List.Tot.Base.splitAt n l`.

    When `n <= length l` the first part has length `n` and the second
    `length l - n`; otherwise the first part is all of `l` and the second is
    empty. *)
let rec splitAt_length
  (#a:Type)
  (n:nat)
  (l:list a)
  : Lemma (requires True)
    (ensures begin
      let l_1, l_2 = splitAt n l in
      if length l < n then
        length l_1 == length l /\ length l_2 == 0
      else
        length l_1 == n /\ length l_2 = length l - n
    end)
    (decreases n)
=
  if n = 0 then ()
  else
    match l with
    | [] -> ()
    | _::xs -> splitAt_length (n-1) xs

(*| Splitting at `n1` and then splitting the rest at `n2` agrees with splitting
    at `n1 + n2`: the first part of the latter is the concatenation of the two
    first parts, and the remainders are equal. *)
let rec splitAt_assoc
  (#a:Type)
  (n1 n2:nat)
  (l:list a)
  : Lemma (requires True)
    (ensures begin
      let l1, l2 = splitAt n1 l in
      let l2, l3 = splitAt n2 l2 in
      let l1', l2' = splitAt (n1+n2) l in
      l1' ==  l1 @ l2 /\ l2' == l3
    end)
    (decreases n1)
=
  if n1 = 0 then ()
  else
    match l with
    | [] -> ()
    | x :: xs -> splitAt_assoc (n1-1) n2 xs


(*| Splitting a list at its length gives the whole list and the empty list. *)
let rec splitAt_length_total (#a:Type) (l:list a)
  : Lemma (requires True) (ensures (splitAt (length l) l == (l, []))) (decreases l)
=
  match l with
  | [] -> ()
  | x :: xs -> splitAt_length_total xs


(*| When `n <= length l`, appending the two parts of
    `FStar.List.Tot.Base.splitAt n l` gives back `l`, and the first part has
    length `n`.

    ```fstar
    let split_then_join (l: list int) (n: nat{n <= length l})
      : Lemma (let l1, l2 = splitAt n l in l1 @ l2 == l)
      = FStar.List.Pure.Properties.lemma_splitAt_append n l
    ``` *)
let rec lemma_splitAt_append (#a:Type) (n:nat) (l:list a) :
  Lemma
    (requires n <= length l)
    (ensures (let l1, l2 = splitAt n l in
              append l1 l2 == l /\ length l1 = n)) =
  match n with
  | 0 -> ()
  | _ ->
    match l with
    | [] -> ()
    | x :: xs -> lemma_splitAt_append (n-1) xs


(*| Splitting `l1 @ l2` at `length l1` gives back `l1` and `l2`. *)
let rec lemma_append_splitAt (#t:Type) (l1 l2:list t) :
  Lemma
    (ensures (splitAt (length l1) (append l1 l2) == (l1, l2))) =
  match l1 with
  | [] -> ()
  | _ -> lemma_append_splitAt (tl l1) l2


(*| Characterizes `FStar.List.Tot.Base.splitAt`: for `n <= length l`,
    `splitAt n l == (l1, l2)` holds exactly when `l == l1 @ l2` and
    `length l1 = n`. *)
let lemma_splitAt (#t: Type) (l l1 l2:list t) (n:nat{n <= length l}) :
  Lemma (splitAt n l == (l1, l2) <==> l == l1 @ l2 /\ length l1 = n) =
  lemma_splitAt_append n l;
  lemma_append_splitAt l1 l2


(*| When `n < length l`, the second part of `FStar.List.Tot.Base.splitAt n l` is
    nonempty and its head is `FStar.List.Tot.Base.index l n`. *)
let rec lemma_splitAt_index_hd (#t:Type) (n:nat) (l:list t) :
  Lemma
    (requires (n < length l))
    (ensures (let l1, l2 = splitAt n l in
              splitAt_length n l;
              length l2 > 0 /\ hd l2 == index l n)) =
  let x :: xs = l in
  match n with
  | 0 -> ()
  | _ -> lemma_splitAt_index_hd (n - 1) (tl l)


(*| If the first `i` elements of `l1` and `l2` agree, then so do their first
    `j` elements for any `j <= i`.

    Agreement is stated on the first components of
    `FStar.List.Tot.Base.splitAt`; `i` must be at most both lengths. *)
let rec lemma_splitAt_shorten_left
    (#t:Type) (l1 l2:list t) (i:nat{i <= length l1 /\ i <= length l2}) (j:nat{j <= i}) :
  Lemma
    (requires (fst (splitAt i l1) == fst (splitAt i l2)))
    (ensures (fst (splitAt j l1) == fst (splitAt j l2))) =
  match j with
  | 0 -> ()
  | _ ->
    lemma_splitAt_shorten_left (tl l1) (tl l2) (i-1) (j-1)

(*| Indexing the first part of `FStar.List.Tot.Base.splitAt i l` at `j < i` is
    the same as indexing `l` at `j`. Requires `i <= length l`. *)
let rec lemma_splitAt_reindex_left (#t:Type) (i:nat) (l:list t) (j:nat) :
  Lemma
    (requires i <= length l /\ j < i)
    (ensures (
        let left, right = splitAt i l in
        splitAt_length i l;
        j < length left /\ index left j == index l j)) =
  match i, j with
  | 1, _ | _, 0 -> ()
  | _ -> lemma_splitAt_reindex_left (i - 1) (tl l) (j - 1)


(*| Indexing the second part of `FStar.List.Tot.Base.splitAt i l` at `j` is the
    same as indexing `l` at `j + i`. Requires `i <= length l` and
    `j + i < length l`. *)
let rec lemma_splitAt_reindex_right (#t:Type) (i:nat) (l:list t) (j:nat) :
  Lemma
    (requires i <= length l /\ j + i < length l)
    (ensures (
        let left, right = splitAt i l in
        splitAt_length i l;
        j < length right /\ index right j == index l (j + i))) =
  match i with
  | 0 -> ()
  | _ -> lemma_splitAt_reindex_right (i - 1) (tl l) j


(** Properties of split3 *)


(*| The three parts `(a, b, c)` of `FStar.List.Tot.Base.split3 l n` rebuild the
    list: `l == append a (b :: c)`. *)
let lemma_split3_append (#t:Type) (l:list t) (n:nat{n < length l}) :
  Lemma
    (requires True)
    (ensures (
        let a, b, c = split3 l n in
        l == append a (b :: c))) =
  lemma_splitAt_append n l


(*| The middle element of `FStar.List.Tot.Base.split3 l n` is
    `FStar.List.Tot.Base.index l n`. *)
let lemma_split3_index (#t:Type) (l:list t) (n:nat{n < length l}) :
  Lemma
    (requires True)
    (ensures (
        let a, b, c = split3 l n in
        b == index l n)) =
  lemma_splitAt_index_hd n l


(*| In `FStar.List.Tot.Base.split3 l n`, the left part has length `n` and the
    right part has length `length l - n - 1`. *)
let lemma_split3_length (#t:Type) (l:list t) (n:nat{n < length l}) :
  Lemma
    (requires True)
    (ensures (
        let a, b, c = split3 l n in
        length a = n /\ length c = length l - n - 1)) =
  splitAt_length n l


(*| If the first `n + 1` elements of `l1` and `l2` agree, then
    `FStar.List.Tot.Base.split3` at `n` gives the same left part and the same
    middle element on both lists. *)
let lemma_split3_on_same_leftprefix
    (#t:Type) (l1 l2:list t) (n:nat{n < length l1 /\ n < length l2}) :
  Lemma
    (requires (fst (splitAt (n+1) l1) == fst (splitAt (n+1) l2)))
    (ensures (let a1, b1, c1 = split3 l1 n in
              let a2, b2, c2 = split3 l2 n in
              a1 == a2 /\ b1 == b2)) =
  let a1, b1, c1 = split3 l1 n in
  let a2, b2, c2 = split3 l2 n in
  lemma_split3_append l1 n;
  lemma_split3_append l2 n;
  lemma_split3_length l1 n;
  lemma_split3_length l2 n;
  append_l_cons b1 c1 a1;
  append_l_cons b2 c2 a2;
  // assert ((a1 @ [b1]) @ c1 == l1);
  // assert ((a2 @ [b2]) @ c2 == l2);
  let x1, y1 = splitAt (n+1) l1 in
  let x2, y2 = splitAt (n+1) l2 in
  lemma_splitAt_append (n+1) l1;
  lemma_splitAt_append (n+1) l2;
  splitAt_length (n+1) l1;
  splitAt_length (n+1) l2;
  // assert (x1 @ y1 == (a1 @ [b1]) @ c1);
  // assert (x2 @ y2 == (a2 @ [b2]) @ c2);
  append_length_inv_head x1 y1 (append a1 [b1]) c1;
  append_length_inv_head x2 y2 (append a2 [b2]) c2;
  // assert (a1 @ [b1] == a2 @ [b2]);
  append_length_inv_tail a1 [b1] a2 [b2];
  // assert (a1 == a2 /\ b1 == b2);
  ()


(*| Relates `FStar.List.Tot.Base.split3` to `FStar.List.Tot.Base.unsnoc` when `n`
    is not the last index: with `(a, b, c) = split3 l n`, the list `c` is
    nonempty and `append a (b :: fst (unsnoc c))` is `fst (unsnoc l)`. *)
let rec lemma_split3_unsnoc (#t:Type) (l:list t) (n:nat{n < length l}) :
  Lemma
    (requires (n <> length l - 1))
    (ensures (
        let a, b, c = split3 l n in
        lemma_split3_length l n;
        length c > 0 /\ (
          let xs, x = unsnoc l in
          let ys, y = unsnoc c in
          append a (b :: ys) == xs))) =
  match n with
  | 0 -> ()
  | _ -> lemma_split3_unsnoc (tl l) (n-1)


(*| When `i` is not the last index of `l`, `FStar.List.Tot.Base.split3` at `i`
    gives the same left part and middle element on `l` and on
    `fst (unsnoc l)`; in particular `i` is a valid index of the latter. *)
let lemma_unsnoc_split3 (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (requires (i <> length l - 1))
    (ensures (
        let xs, x = unsnoc l in
        i < length xs /\ (
            let a0, b0, c0 = split3 l i in
            let a1, b1, c1 = split3 xs i in
            a0 == a1 /\ b0 == b1))) =
  let xs, x = unsnoc l in
  lemma_unsnoc_length l;
  let a0, b0, c0 = split3 l i in
  let a1, b1, c1 = split3 xs i in
  splitAt_length_total xs;
  // assert (fst (splitAt (length xs) xs) == xs);
  // assert (fst (splitAt (length xs) xs) == fst (splitAt (length xs) l));
  // assert (i+1 <= length xs);
  lemma_splitAt_shorten_left xs l (length xs) (i+1);
  // assert (fst (splitAt (i+1) xs) == fst (splitAt (i+1) l));
  lemma_split3_on_same_leftprefix l xs i

(*| If the right part `c` of `FStar.List.Tot.Base.split3 l i` is nonempty, then
    `i + 1 < length l` and the head of `c` is `FStar.List.Tot.Base.index l (i + 1)`. *)
let rec lemma_split3_r_hd (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (ensures (let a, b, c = split3 l i in
              lemma_split3_length l i;
              length c > 0 ==> i + 1 < length l /\ hd c == index l (i + 1))) =
  match i with
  | 0 -> ()
  | _ -> lemma_split3_r_hd (tl l) (i - 1)
