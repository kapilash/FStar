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
(**
This module states and proves some properties about pure and total
operations on lists.

@summary Properties of pure total operations on lists
*)
module FStar.List.Tot.Properties
open FStar.List.Tot.Base

(** A list indexed by its length **)
(*| The type of lists of length exactly `n`. *)
let llist a (n:nat) = l:list a {length l = n}

(** Properties about mem **)

(* TODO: replace [mem] with [memP] in relevant lemmas and define the right
   SMTPat to automatically recover lemmas about [mem] for types with
   decidable equality *)

(*| For types with decidable equality, the boolean `FStar.List.Tot.Base.mem`
    agrees with the propositional `FStar.List.Tot.Base.memP`.

    Triggered automatically when both `mem x l` and `memP x l` appear. *)
val mem_memP
  (#a: eqtype)
  (x: a)
  (l: list a)
: Lemma (ensures (mem x l <==> memP x l))
        [SMTPat (mem x l); SMTPat (memP x l)]

(*| Every element obtained with `FStar.List.Tot.Base.index` is a member of the
    list. Triggered automatically on `memP (index l i) l`. *)
val lemma_index_memP (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (ensures (index l i `memP` l))
    [SMTPat (index l i `memP` l)]

(*| Nothing is a member of the empty list: from `memP x []` one can derive
    `False`. *)
val memP_empty : #a: Type -> x:a ->
  Lemma (requires (memP x []))
        (ensures False)

(*| Characterizes `FStar.List.Tot.Base.existsb`: it returns `true` exactly when
    some member `x` of the list satisfies `f x`, with membership as
    `FStar.List.Tot.Base.memP`. *)
val memP_existsb: #a: Type -> f:(a -> Tot bool) -> xs:list a ->
  Lemma(ensures (existsb f xs <==> (exists (x:a). (f x = true /\ memP x xs))))

(*| If `x` is a member of `l`, then `f x` is a member of `map f l`. *)
val memP_map_intro
  (#a #b: Type)
  (f: a -> Tot b)
  (x: a)
  (l: list a)
: Lemma
  (requires True)
  (ensures (memP x l ==> memP (f x) (map f l)))

(*| Every member of `map f l` is `f x` for some member `x` of `l`. *)
val memP_map_elim
  (#a #b: Type)
  (f: a -> Tot b)
  (y: b)
  (l: list a)
: Lemma
  (requires True)
  (ensures (memP y (map f l) ==> (exists (x : a) . memP x l /\ f x == y)))

(*| Nothing is a member of the empty list: from `mem x []` one can derive
    `False`. The `eqtype` counterpart of
    `FStar.List.Tot.Properties.memP_empty`. *)
val mem_empty : #a:eqtype -> x:a ->
  Lemma (requires (mem x []))
        (ensures False)

(*| Characterizes `FStar.List.Tot.Base.existsb`: it returns `true` exactly when
    some member `x` of the list satisfies `f x`, with membership as
    `FStar.List.Tot.Base.mem`. *)
val mem_existsb: #a:eqtype -> f:(a -> Tot bool) -> xs:list a ->
  Lemma(ensures (existsb f xs <==> (exists (x:a). (f x = true /\ mem x xs))))

(*| An element is a member of a list exactly when its
    `FStar.List.Tot.Base.count` in the list is positive. *)
val mem_count
  (#a: eqtype)
  (l: list a)
  (x: a)
: Lemma
  (mem x l <==> count x l > 0)

(** Properties about rev **)

(*| The length of `rev_acc l acc` is the sum of the lengths of `l` and `acc`. *)
val rev_acc_length : l:list 'a -> acc:list 'a ->
  Lemma (requires True)
        (ensures (length (rev_acc l acc) = length l + length acc))

(*| Reversing a list preserves its length. *)
val rev_length : l:list 'a ->
  Lemma (requires True)
        (ensures (length (rev l) = length l))

(*| The members of `rev_acc l acc` are exactly the members of `l` and of `acc`. *)
val rev_acc_memP : #a:Type -> l:list a -> acc:list a -> x:a ->
  Lemma (requires True)
        (ensures (memP x (rev_acc l acc) <==> (memP x l \/ memP x acc)))

(*| A list and its reverse have the same members, with membership as
    `FStar.List.Tot.Base.memP`. *)
val rev_memP : #a:Type -> l:list a -> x:a ->
  Lemma (requires True)
        (ensures (memP x (rev l) <==> memP x l))

(*| A list and its reverse have the same members, with membership as
    `FStar.List.Tot.Base.mem`. *)
val rev_mem : #a:eqtype -> l:list a -> x:a ->
  Lemma (requires True)
        (ensures (mem x (rev l) <==> mem x l))

(** Properties about append **)

(*| The empty list is a left identity of append: `[] @ l == l`. *)
val append_nil_l: l:list 'a ->
  Lemma (requires True)
        (ensures ([]@l == l))

(*| The empty list is a right identity of append: `l @ [] == l`.
    Triggered automatically on `l @ []`. *)
val append_l_nil: l:list 'a ->
  Lemma (requires True)
        (ensures (l@[] == l)) [SMTPat (l@[])]

(*| Appending to a cons cell: `(hd :: tl) @ l == hd :: (tl @ l)`. *)
val append_cons_l: hd:'a -> tl:list 'a -> l:list 'a ->
  Lemma (requires True)
        (ensures (((hd::tl)@l) == (hd::(tl@l))))

(*| Moves the head of the right operand to the left one:
    `l @ (hd :: tl) == (l @ [hd]) @ tl`. *)
val append_l_cons: hd:'a -> tl:list 'a -> l:list 'a ->
  Lemma (requires True)
        (ensures ((l@(hd::tl)) == ((l@[hd])@tl)))

(*| Append is associative: `l1 @ (l2 @ l3) == (l1 @ l2) @ l3`.

    There is no SMT pattern, so call it when a proof needs to reassociate.

    ```fstar
    let reassociate (l1 l2 l3: list int) : Lemma (l1 @ (l2 @ l3) == (l1 @ l2) @ l3) =
      FStar.List.Tot.Properties.append_assoc l1 l2 l3
    ``` *)
val append_assoc: l1:list 'a -> l2:list 'a -> l3:list 'a ->
  Lemma (requires True)
        (ensures ((l1@(l2@l3)) == ((l1@l2)@l3)))

(*| The length of `l1 @ l2` is the sum of the lengths of `l1` and `l2`.

    Triggered automatically on `length (l1 @ l2)`, so it rarely needs to be
    called.

    ```fstar
    let length_of_append (l1 l2: list nat)
      : Lemma (length (l1 @ l2) == length l1 + length l2)
      = ()
    ``` *)
val append_length: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures (length (l1@l2) = length l1 + length l2)) [SMTPat (length (l1 @ l2))]

(*| An element is a member of `l1 @ l2` exactly when it is a member of `l1` or
    of `l2`, with membership as `FStar.List.Tot.Base.mem`. *)
val append_mem: #t:eqtype ->  l1:list t
              -> l2:list t
              -> a:t
              -> Lemma (requires True)
                       (ensures (mem a (l1@l2) = (mem a l1 || mem a l2)))
                       (* [SMTPat (mem a (l1@l2))] *)

(*| An element is a member of `append l1 l2` exactly when it is a member of
    `l1` or of `l2`, with membership as `FStar.List.Tot.Base.memP`. *)
val append_memP: #t:Type ->  l1:list t
              -> l2:list t
              -> a:t
              -> Lemma (requires True)
                       (ensures (memP a (l1 `append` l2) <==> (memP a l1 \/ memP a l2)))
                       (* [SMTPat (mem a (l1@l2))] *)

(*| The same as `FStar.List.Tot.Properties.append_mem`, stated for all elements
    at once. *)
val append_mem_forall: #a:eqtype -> l1:list a
              -> l2:list a
              -> Lemma (requires True)
                       (ensures (forall a. mem a (l1@l2) = (mem a l1 || mem a l2)))

(*| The same as `FStar.List.Tot.Properties.append_memP`, stated for all
    elements at once. *)
val append_memP_forall: #a:Type -> l1:list a
              -> l2:list a
              -> Lemma (requires True)
                       (ensures (forall a. memP a (l1 `append` l2) <==> (memP a l1 \/ memP a l2)))


(*| The number of occurrences of an element in `l1 @ l2` is the sum of its
    occurrences in `l1` and in `l2`. *)
val append_count: #t:eqtype ->  l1:list t
              -> l2:list t
              -> a:t
              -> Lemma (requires True)
                       (ensures (count a (l1@l2) = (count a l1 + count a l2)))

(*| The same as `FStar.List.Tot.Properties.append_count`, stated for all
    elements at once. *)
val append_count_forall: #a:eqtype ->  l1:list a
              -> l2:list a
              -> Lemma (requires True)
                       (ensures (forall a. count a (l1@l2) = (count a l1 + count a l2)))
                       (* [SMTPat (l1@l2)] *)

(*| If `l1 @ l2` is empty, then both `l1` and `l2` are empty. *)
val append_eq_nil: l1:list 'a -> l2:list 'a ->
  Lemma (requires (l1@l2 == []))
        (ensures (l1 == [] /\ l2 == []))

(*| If `l1 @ l2` is the singleton `[x]`, then one of the two lists is `[x]` and
    the other is empty. *)
val append_eq_singl: l1:list 'a -> l2:list 'a -> x:'a ->
  Lemma (requires (l1@l2 == [x]))
        (ensures ((l1 == [x] /\ l2 == []) \/ (l1 == [] /\ l2 == [x])))

(*| Append is cancellable on the left: `l @ l1 == l @ l2` implies `l1 == l2`. *)
val append_inv_head: l:list 'a -> l1:list 'a -> l2:list 'a ->
  Lemma (requires ((l@l1) == (l@l2)))
        (ensures (l1 == l2))

(*| Append is cancellable on the right: `l1 @ l == l2 @ l` implies `l1 == l2`. *)
val append_inv_tail: l:list 'a -> l1:list 'a -> l2:list 'a ->
  Lemma (requires ((l1@l) == (l2@l)))
        (ensures (l1 == l2))

(*| If two appends are equal and their left operands have the same length, then
    the left operands are equal and the right operands are equal. *)
val append_length_inv_head
  (#a: Type)
  (left1 right1 left2 right2: list a)
: Lemma
  (requires (append left1 right1 == append left2 right2 /\ length left1 == length left2))
  (ensures (left1 == left2 /\ right1 == right2))

(*| If two appends are equal and their right operands have the same length,
    then the left operands are equal and the right operands are equal. *)
val append_length_inv_tail
  (#a: Type)
  (left1 right1 left2 right2: list a)
: Lemma
  (requires (append left1 right1 == append left2 right2 /\ length right1 == length right2))
  (ensures (left1 == left2 /\ right1 == right2))

(*| If two appends are equal and either their left operands or their right
    operands have the same length, then both pairs of operands are equal.

    Combines `FStar.List.Tot.Properties.append_length_inv_head` and
    `FStar.List.Tot.Properties.append_length_inv_tail` as an implication. *)
val append_injective #a (l0 l0':list a)
                        (l1 l1':list a)
  : Lemma
    (ensures
      (length l0 == length l0' \/ length l1 == length l1') /\
      append l0 l1 == append l0' l1' ==>
      l0 == l0' /\ l1 == l1')

(*| The last element of `l1 @ l2` is the last element of `l2`, when `l2` is
    nonempty. *)
val lemma_append_last (#a:Type) (l1 l2:list a) :
  Lemma
    (requires (length l2 > 0))
    (ensures (last (l1 @ l2) == last l2))

(** Properties mixing rev and append **)

(*| Reverses a list by appending each head after the reversed tail.

    A naive specification of `FStar.List.Tot.Base.rev`, which it equals by
    `FStar.List.Tot.Properties.rev_rev'`; convenient for inductive proofs. *)
let rec rev' (#a:Type) (xs : list a) : list a =
  match xs with
  | [] -> []
  | hd::tl -> (rev' tl)@[hd]
(*| An alias of `FStar.List.Tot.Properties.rev'`. *)
let rev'T = rev'

(*| `rev_acc l acc` is the naive reverse of `l` followed by `acc`. *)
val rev_acc_rev': l:list 'a -> acc:list 'a ->
  Lemma (requires (True))
        (ensures ((rev_acc l acc) == ((rev' l)@acc)))

(*| `FStar.List.Tot.Base.rev` equals the naive reverse
    `FStar.List.Tot.Properties.rev'`. *)
val rev_rev': l:list 'a ->
  Lemma (requires True)
        (ensures ((rev l) == (rev' l)))

(*| The naive reverse of `l1 @ l2` is the naive reverse of `l2` followed by
    that of `l1`. *)
val rev'_append: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures ((rev' (l1@l2)) == ((rev' l2)@(rev' l1))))

(*| Reversing an append swaps and reverses the operands:
    `rev (l1 @ l2) == rev l2 @ rev l1`. *)
val rev_append: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures ((rev (l1@l2)) == ((rev l2)@(rev l1))))

(*| The naive reverse `FStar.List.Tot.Properties.rev'` is an involution. *)
val rev'_involutive : l:list 'a ->
  Lemma (requires True)
        (ensures (rev' (rev' l) == l))

(*| Reversing a list twice gives back the original list.

    ```fstar
    let rev_rev_example (l: list int) : Lemma (rev (rev l) == l) =
      FStar.List.Tot.Properties.rev_involutive l
    ``` *)
val rev_involutive : l:list 'a ->
  Lemma (requires True)
        (ensures (rev (rev l) == l))

(** Properties about snoc *)

(*| Adding an element at the end with `FStar.List.Tot.Base.snoc` increases the
    length by one. *)
val lemma_snoc_length : (lx:(list 'a & 'a)) ->
  Lemma (requires True)
        (ensures (length (snoc lx) = length (fst lx) + 1))

(** Reverse induction principle **)

(*| An induction principle phrased with `FStar.List.Tot.Properties.rev'`: if `p`
    holds of `[]` and is preserved from `rev' tl` to `rev' (hd :: tl)`, then it
    holds of `rev' l` for every `l`. *)
val rev'_list_ind: p:(list 'a -> Tot bool) -> l:list 'a ->
  Lemma (requires ((p []) /\ (forall hd tl. p (rev' tl) ==> p (rev' (hd::tl)))))
        (ensures (p (rev' l)))

(*| Reverse induction on lists: if `p` holds of `[]` and `p l` implies
    `p (l @ [x])` for all `l` and `x`, then `p` holds of every list.

    Note that in the statement the quantified list is named `hd` and the added
    element `tl`. The property `p` must be a boolean function. *)
val rev_ind: p:(list 'a -> Tot bool) -> l:list 'a ->
  Lemma (requires ((p []) /\ (forall hd tl. p hd ==> p (hd@[tl]))))
        (ensures (p l))

(** Properties about iterators **)

(*| `FStar.List.Tot.Base.map` preserves length. Triggered automatically on
    `map f l`. *)
val map_lemma: f:('a -> Tot 'b)
             -> l:(list 'a)
             -> Lemma (requires True)
                      (ensures (length (map f l)) = length l)
                      [SMTPat (map f l)]

(** Properties about unsnoc *)

(*| `FStar.List.Tot.Base.snoc` undoes `FStar.List.Tot.Base.unsnoc` on a
    nonempty list. Triggered automatically on `snoc (unsnoc l)`. *)
val lemma_unsnoc_snoc: #a:Type -> l:list a{length l > 0} ->
  Lemma (requires True)
    (ensures (snoc (unsnoc l) == l))
    [SMTPat (snoc (unsnoc l))]

(*| `FStar.List.Tot.Base.unsnoc` undoes `FStar.List.Tot.Base.snoc`. Triggered
    automatically on `unsnoc (snoc lx)`. *)
val lemma_snoc_unsnoc: #a:Type -> lx:(list a & a) ->
  Lemma (requires True)
    (ensures (unsnoc (snoc lx) == lx))
    [SMTPat (unsnoc (snoc lx))]

(*| The first component of `FStar.List.Tot.Base.unsnoc l` is one element shorter
    than the nonempty list `l`. *)
val lemma_unsnoc_length: #a:Type -> l:list a{length l > 0} ->
  Lemma (requires True)
    (ensures (length (fst (unsnoc l)) == length l - 1))

(*| `unsnoc (l1 @ l2)`, for a nonempty `l2`, keeps `l1` in front of the prefix
    of `unsnoc l2` and has the same last element. *)
val lemma_unsnoc_append (#a:Type) (l1 l2:list a) :
  Lemma
    (requires (length l2 > 0)) // the [length l2 = 0] is trivial
    (ensures (
        let al, a = unsnoc (l1 @ l2) in
        let bl, b = unsnoc l2 in
        al == l1 @ bl /\ a == b))

(*| The element split off by `FStar.List.Tot.Base.unsnoc` is
    `FStar.List.Tot.Base.last l`, which is also the element at index
    `length l - 1`. *)
val lemma_unsnoc_is_last (#t:Type) (l:list t) :
  Lemma
    (requires (length l > 0))
    (ensures (snd (unsnoc l) == last l /\ snd (unsnoc l) == index l (length l - 1))) 

(*| Indexing the prefix returned by `FStar.List.Tot.Base.unsnoc` at
    `i < length l - 1` is the same as indexing `l` at `i`. *)
val lemma_unsnoc_index (#t:Type) (l:list t) (i:nat) :
  Lemma
    (requires (length l > 0 /\ i < length l - 1))
    (ensures (
        i < length (fst (unsnoc l)) /\
        index (fst (unsnoc l)) i == index l i))

(** Definition and properties about [split_using] *)

(*| Splits a list just before the first occurrence of `x`, which must be a
    member of the list.

    Ghost, because it compares elements with propositional equality. The
    second part starts with `x`; see
    `FStar.List.Tot.Properties.lemma_split_using`. *)
let rec split_using (#t:Type) (l:list t) (x:t{x `memP` l}) :
  GTot (list t & list t) =
  match l with
  | [_] -> [], l
  | a :: rest ->
    if a == x then (
      [], l
    ) else (
      let l1', l2' = split_using rest x in
      a :: l1', l2'
    )

(*| Specifies `FStar.List.Tot.Properties.split_using`: the parts `l1` and `l2`
    append to the original list, `x` is not a member of `l1`, and `l2` is
    nonempty with head `x`. *)
val lemma_split_using (#t:Type) (l:list t) (x:t{x `memP` l}) :
  Lemma
    (ensures (
        let l1, l2 = split_using l x in
         length l2 > 0 /\
        ~(x `memP` l1) /\
         hd l2 == x /\
        append l1 l2 == l))

(** Definition of [index_of] *)

(*| Returns the index of the first occurrence of `x` in the list, which must be
    a member.

    Ghost, because it compares elements with propositional equality. The result
    `i` satisfies `index l i == x`. *)
let rec index_of (#t:Type) (l:list t) (x:t{x `memP` l}) :
  GTot (i:nat{i < length l /\ index l i == x}) =
  match l with
  | [_] -> 0
  | a :: rest ->
    if a == x then (
      0
    ) else (
      1 + index_of rest x
    )


(** Properties about partition **)

(*| An element is a member of `l` exactly when it is a member of one of the two
    parts of `FStar.List.Tot.Base.partition f l`. *)
val partition_mem: #a:eqtype -> f:(a -> Tot bool)
                  -> l:list a
                  -> x:a
                  -> Lemma (requires True)
                          (ensures (let l1, l2 = partition f l in
                                    mem x l = (mem x l1 || mem x l2)))

(*| The same as `FStar.List.Tot.Properties.partition_mem`, stated for all
    elements at once. *)
val partition_mem_forall: #a:eqtype -> f:(a -> Tot bool)
                  -> l:list a
                  -> Lemma (requires True)
                          (ensures (let l1, l2 = partition f l in
                                    (forall x. mem x l = (mem x l1 || mem x l2))))

(*| Every member of the first part of `FStar.List.Tot.Base.partition p l`
    satisfies `p`, and no member of the second part does. *)
val partition_mem_p_forall: #a:eqtype -> p:(a -> Tot bool)
                  -> l:list a
                  -> Lemma (requires True)
                          (ensures (let l1, l2 = partition p l in
                                    (forall x. mem x l1 ==> p x) /\ (forall x. mem x l2 ==> not (p x))))

(*| The number of occurrences of an element in `l` is the sum of its
    occurrences in the two parts of `FStar.List.Tot.Base.partition f l`. *)
val partition_count: #a:eqtype -> f:(a -> Tot bool)
                  -> l:list a
                  -> x:a
                  -> Lemma (requires True)
                           (ensures (count x l = (count x (fst (partition f l)) + count x (snd (partition f l)))))

(*| The same as `FStar.List.Tot.Properties.partition_count`, stated for all
    elements at once. *)
val partition_count_forall: #a:eqtype -> f:(a -> Tot bool)
                  -> l:list a
                  -> Lemma (requires True)
                           (ensures (forall x. count x l = (count x (fst (partition f l)) + count x (snd (partition f l)))))
                           (* [SMTPat (partitionT f l)] *)

(** Properties about subset **)

(*| Characterizes `FStar.List.Tot.Base.subset`: `subset la lb` holds exactly
    when every member of `la` is a member of `lb`.

    Triggered automatically on `subset la lb`. *)
val mem_subset (#a: eqtype) (la lb: list a)
    : Lemma (subset la lb <==> (forall x. mem x la ==> mem x lb))
            [SMTPat (subset la lb)]

(* NOTE: This is implied by mem_subset above, kept for compatibility *)
(*| Every list is a subset of itself, as computed by
    `FStar.List.Tot.Base.subset`.

    Implied by `FStar.List.Tot.Properties.mem_subset`; kept for compatibility. *)
val subset_reflexive (#a: eqtype) (l: list a)
    : Lemma (subset l l)

(** Correctness of quicksort **)

(*| `FStar.List.Tot.Base.sortWith f l` is a permutation of `l`: every element
    occurs as many times in it as in `l`.

    Together with `FStar.List.Tot.Properties.sortWith_sorted` this is the
    correctness of the sort. No precondition on `f` is needed. *)
val sortWith_permutation: #a:eqtype -> f:(a -> a -> Tot int) -> l:list a ->
  Lemma (requires True)
        (ensures (forall x. count x l = count x (sortWith f l)))

(*| Holds when every two consecutive elements `x`, `y` of the list satisfy
    `f x y`.

    With a transitive `f` this means `f` relates every element to all later
    ones. `FStar.List.Tot.Properties.sortWith_sorted` uses it with
    `FStar.List.Tot.Base.bool_of_compare`. *)
let rec sorted (#a:Type) (f : a -> a -> Tot bool) : list a -> bool = function
  | []
  | [_] -> true
  | x::y::tl -> f x y && sorted f (y::tl)

(*| The proposition that the boolean relation `f` is a total order: reflexive,
    antisymmetric, transitive and total.

    `FStar.List.Tot.Properties.sortWith_sorted` requires it of
    `FStar.List.Tot.Base.bool_of_compare f`, which is reflexive only when
    `f x x < 0` for every `x`. *)
type total_order (#a:Type) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. f a1 a2 /\ f a2 a1  ==> a1 == a2)         (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
    /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                       (* totality *)

(*| Under `FStar.List.Tot.Properties.total_order f`, joining two sorted lists
    around a pivot gives a sorted list, provided no member `y` of `l1`
    satisfies `f pivot y` and every member `y` of `l2` does.

    Triggered automatically on `sorted f (l1 @ (pivot :: l2))`. This is the
    step used in the proof of quicksort. *)
val append_sorted: #a:eqtype
               ->  f:(a -> a -> Tot bool)
               ->  l1:list a{sorted f l1}
               ->  l2:list a{sorted f l2}
               ->  pivot:a
               ->  Lemma (requires (total_order #a f
                                    /\ (forall y. mem y l1 ==> not(f pivot y))
                                    /\ (forall y. mem y l2 ==> f pivot y)))
                        (ensures (sorted f (l1@(pivot::l2))))
                        [SMTPat (sorted f (l1@(pivot::l2)))]

(*| `FStar.List.Tot.Base.sortWith f l` is sorted according to
    `FStar.List.Tot.Base.bool_of_compare f`, and has the same members as `l`.

    The precondition asks `bool_of_compare f` to be a
    `FStar.List.Tot.Properties.total_order`. Since `bool_of_compare f x y` is
    `f x y < 0`, `f` must return a negative number on equal elements, as a
    comparison meaning "less than or equal" does; a comparison returning 0 on
    equal elements does not qualify.
    `FStar.List.Tot.Properties.sortWith_permutation` needs no precondition. *)
val sortWith_sorted: #a:eqtype -> f:(a -> a -> Tot int) -> l:list a ->
  Lemma (requires (total_order #a (bool_of_compare f)))
        (ensures ((sorted (bool_of_compare f) (sortWith f l)) /\ (forall x. mem x l = mem x (sortWith f l))))

(** Properties of [noRepeats] *)

(*| The empty list has no repeated elements, as computed by
    `FStar.List.Tot.Base.noRepeats`. *)
val noRepeats_nil
  (#a: eqtype)
: Lemma
  (ensures (noRepeats #a []))

(*| Adding to the front of a list without repetitions an element that is not a
    member of it gives a list without repetitions. *)
val noRepeats_cons
  (#a: eqtype)
  (h: a)
  (tl: list a)
: Lemma
  (requires ((~ (mem h tl)) /\ noRepeats tl))
  (ensures (noRepeats #a (h::tl)))

(*| If `l1 @ l2` has no repeated elements, then neither has `l1` nor `l2`, and
    they have no member in common. *)
val noRepeats_append_elim
  (#a: eqtype)
  (l1 l2: list a)
: Lemma
  (requires (noRepeats (l1 @ l2)))
  (ensures (noRepeats l1 /\ noRepeats l2 /\ (forall x . mem x l1 ==> ~ (mem x l2))))

(*| If `l1` and `l2` have no repeated elements and no member in common, then
    `l1 @ l2` has no repeated elements. *)
val noRepeats_append_intro
  (#a: eqtype)
  (l1 l2: list a)
: Lemma
  (requires (noRepeats l1 /\ noRepeats l2 /\ (forall x . mem x l1 ==> ~ (mem x l2))))
  (ensures (noRepeats (l1 @ l2)))

(** Properties of [no_repeats_p] *)

(*| The empty list has no repeated elements, as stated by
    `FStar.List.Tot.Base.no_repeats_p`. *)
val no_repeats_p_nil
  (#a: Type)
: Lemma
  (ensures (no_repeats_p #a []))

(*| Adding to the front of a list without repetitions an element that is not a
    member of it gives a list without repetitions, with membership as
    `FStar.List.Tot.Base.memP`. *)
val no_repeats_p_cons
  (#a: Type)
  (h: a)
  (tl: list a)
: Lemma
  (requires ((~ (memP h tl)) /\ no_repeats_p tl))
  (ensures (no_repeats_p #a (h::tl)))

(*| If `append l1 l2` has no repeated elements, then neither has `l1` nor `l2`,
    and they have no member in common. *)
val no_repeats_p_append_elim
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (requires (no_repeats_p (l1 `append` l2)))
  (ensures (no_repeats_p l1 /\ no_repeats_p l2 /\ (forall x . memP x l1 ==> ~ (memP x l2))))

(*| If `l1` and `l2` have no repeated elements and no member in common, then
    `append l1 l2` has no repeated elements. *)
val no_repeats_p_append_intro
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (requires (no_repeats_p l1 /\ no_repeats_p l2 /\ (forall x . memP x l1 ==> ~ (memP x l2))))
  (ensures (no_repeats_p (l1 `append` l2)))

(*| `append l1 l2` has no repeated elements exactly when `l1` and `l2` have
    none and have no member in common.

    Combines `FStar.List.Tot.Properties.no_repeats_p_append_elim` and
    `FStar.List.Tot.Properties.no_repeats_p_append_intro`. *)
val no_repeats_p_append
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (no_repeats_p (l1 `append` l2) <==> (
    (no_repeats_p l1 /\ no_repeats_p l2 /\ (forall x . memP x l1 ==> ~ (memP x l2)))
  ))

(*| Swapping the operands of an append does not change whether it has repeated
    elements. *)
val no_repeats_p_append_swap
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (no_repeats_p (l1 `append` l2) <==> no_repeats_p (l2 `append` l1))

(*| Exchanging the second and fourth lists of a five-way append (associated to
    the right) does not change whether it has repeated elements. *)
val no_repeats_p_append_permut
  (#a: Type)
  (l1 l2 l3 l4 l5: list a)
: Lemma
  ((no_repeats_p (l1 `append` (l2 `append` (l3 `append` (l4 `append` l5))))) <==> no_repeats_p (l1 `append` (l4 `append` (l3 `append` (l2 `append` l5)))))

(*| A list in which the same nonempty list `l` appears twice, as in
    `l1 @ (l @ (l2 @ (l @ l3)))`, has repeated elements. *)
val no_repeats_p_false_intro
  (#a: Type)
  (l1 l l2 l3: list a)
: Lemma
  (requires (Cons? l))
  (ensures (~ (no_repeats_p (l1 `append` (l `append` (l2 `append` (l `append` l3)))))))

(** Properties of [assoc] *)

(*| Looking up any key in the empty association list gives `None`. *)
val assoc_nil
  (#a: eqtype)
  (#b: Type)
  (x: a)
: Lemma
  (ensures (assoc #a #b x [] == None))

(*| Looking up `x` in an association list whose first pair has key `x` gives
    the value of that pair. *)
val assoc_cons_eq
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (y: b)
  (q: list (a & b))
: Lemma
  (ensures (assoc x ((x, y) :: q) == Some y))

(*| Looking up `x'` in a list whose first pair has a different key `x` is the
    same as looking it up in the rest of the list. *)
val assoc_cons_not_eq
  (#a: eqtype)
  (#b: Type)
  (x x': a)
  (y: b)
  (q: list (a & b))
: Lemma
  (requires (x <> x'))
  (ensures (assoc x' ((x, y) :: q) == assoc x' q))

(*| Looking up `x` in `l1 @ l2` gives the same result as in `l1`, when `x` is
    bound in `l1` or not bound in `l2`. *)
val assoc_append_elim_r
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l1 l2: list (a & b))
: Lemma
  (requires (assoc x l2 == None \/ ~ (assoc x l1 == None)))
  (ensures (assoc x (l1 @ l2) == assoc x l1))

(*| Looking up `x` in `l1 @ l2` gives the same result as in `l2`, when `x` is
    not bound in `l1`. *)
val assoc_append_elim_l
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l1 l2: list (a & b))
: Lemma
  (requires (assoc x l1 == None))
  (ensures (assoc x (l1 @ l2) == assoc x l2))

(*| If `FStar.List.Tot.Base.assoc x l` returns `Some y`, then the pair `(x, y)`
    is a member of `l`. *)
val assoc_memP_some
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (y: b)
  (l: list (a & b))
: Lemma
  (requires (assoc x l == Some y))
  (ensures (memP (x, y) l))

(*| If `FStar.List.Tot.Base.assoc x l` returns `None`, then no pair with key `x`
    is a member of `l`. *)
val assoc_memP_none
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l: list (a & b))
: Lemma
  (requires (assoc x l == None))
  (ensures (forall y . ~ (memP (x, y) l)))

(*| A key is among the first components of an association list exactly when
    `FStar.List.Tot.Base.assoc` finds a value for it. *)
val assoc_mem
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l: list (a & b))
: Lemma
  (ensures (mem x (map fst l) <==> (exists y . assoc x l == Some y)))

(** Properties of [fold_left] *)

(*| An invariant preserved by every step of `FStar.List.Tot.Base.fold_left`
    holds of its result.

    If `p x` implies `p (f x y)` for every member `y` of `l`, then `p x` implies
    `p (fold_left f x l)`. *)
val fold_left_invar
  (#a #b: Type)
  (f: (a -> b -> Tot a))
  (l: list b)
  (p: (a -> prop))
  : Lemma
  (requires forall (x: a) (y: b) . p x ==> memP y l ==> p (f x y) )
  (ensures forall (x: a) . p x ==> p (fold_left f x l))

(*| Folding over `map f_bc l` with `f_aca` is the same as folding over `l` with
    `f_aba`, when `f_aba x y` is `f_aca x (f_bc y)` for all `x` and `y`. *)
val fold_left_map
  (#a #b #c: Type)
  (f_aba: a -> b -> Tot a)
  (f_bc:  b -> Tot c)
  (f_aca: a -> c -> Tot a)
  (l: list b)
  : Lemma
  (requires forall (x: a) (y: b) . f_aba x y == f_aca x (f_bc y) )
  (ensures forall (x : a) . fold_left f_aba x l == fold_left f_aca x (map f_bc l) )

(*| `FStar.List.Tot.Base.map` distributes over append:
    `map f (l1 @ l2) == map f l1 @ map f l2`. *)
val map_append
  (#a #b: Type)
  (f: a -> Tot b)
  (l1 l2: list a)
:
  Lemma
  (ensures map f (l1 @ l2) == map f l1 @ map f l2)

(*| Folding over `l1 @ l2` is folding over `l1` and then continuing over `l2`
    from the result. *)
val fold_left_append
  (#a #b: Type)
  (f: a -> b -> Tot a)
  (l1 l2: list b)
  : Lemma
  (ensures forall x . fold_left f x (l1 @ l2) == fold_left f (fold_left f x l1) l2)

(*| For a monoid with operation `opA` and unit `zeroA`, folding from an
    arbitrary start `x` is `x` combined with the fold from the unit:
    `fold_left opA x l == opA x (fold_left opA zeroA l)`. *)
val fold_left_monoid
  (#a: Type)
  (opA: (a -> a -> Tot a))
  (zeroA: a)
  (l: list a)
: Lemma
  (requires
    (forall u v w . (u `opA` (v `opA` w)) == ((u `opA` v) `opA` w)) /\
    (forall x . (x `opA` zeroA) == x) /\
    (forall x . (zeroA `opA` x) == x))
  (ensures
    forall x .
    (fold_left opA x l) == (x `opA` (fold_left opA zeroA l)))

(*| For a monoid with operation `f` and unit `z`, folding from the unit over
    `l1 @ l2` combines the folds over `l1` and over `l2`. *)
val fold_left_append_monoid
  (#a: Type)
  (f: (a -> a -> Tot a))
  (z: a)
  (l1 l2: list a)
: Lemma
  (requires
    (forall u v w . f u (f v w) == f (f u v) w) /\
    (forall x . f x z == x) /\
    (forall x . f z x == x))
  (ensures
    fold_left f z (l1 @ l2) == f (fold_left f z l1) (fold_left f z l2))

(* Properties of [index] *)

(*| Two lists of the same length that agree at every index are equal. *)
val index_extensionality
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (requires
    (length l1 == length l2 /\
    (forall (i: nat) . i < length l1 ==> index l1 i == index l2 i)))
  (ensures (l1 == l2))

(** Properties of [strict_suffix_of] *)

(*| The empty list is a strict suffix of every nonempty list. *)
val strict_suffix_of_nil (#a: Type) (x: a) (l: list a)
: Lemma
  (requires True)
  (ensures (strict_suffix_of [] (x::l)))

(*| Every list is either empty or has the empty list as a strict suffix. *)
val strict_suffix_of_or_eq_nil (#a: Type) (l: list a)
: Lemma
  (ensures (strict_suffix_of [] l \/ l == []))

(*| The tail `l` is a strict suffix of `x :: l`. *)
val strict_suffix_of_cons (#a: Type) (x: a) (l: list a) :
  Lemma
  (ensures (strict_suffix_of l (x::l)))

(*| `FStar.List.Tot.Base.strict_suffix_of` is transitive.

    Triggered automatically when both `strict_suffix_of l1 l2` and
    `strict_suffix_of l2 l3` appear. *)
val strict_suffix_of_trans (#a: Type) (l1 l2 l3: list a)
: Lemma
  (requires True)
  (ensures ((strict_suffix_of l1 l2 /\ strict_suffix_of l2 l3) ==> strict_suffix_of l1 l3))
  [SMTPat (strict_suffix_of l1 l2); SMTPat (strict_suffix_of l2 l3)]

(*| A strict suffix of a list precedes it in the well-founded order `<<`, so it
    can be used to justify termination. *)
val strict_suffix_of_correct (#a:Type) (l1 l2: list a)
: Lemma
  (requires True)
  (ensures (strict_suffix_of l1 l2 ==> l1 << l2))

(*| `FStar.List.Tot.Base.map` preserves strict suffixes: if `l1` is a strict
    suffix of `l2`, then `map f l1` is a strict suffix of `map f l2`. *)
val map_strict_suffix_of (#a #b: Type) (f: a -> Tot b) (l1: list a) (l2: list a) :
 Lemma
 (requires True)
 (ensures (strict_suffix_of l1 l2 ==> strict_suffix_of (map f l1) (map f l2)))

(*| A member of a strict suffix of `l2` is a member of `l2`. *)
val mem_strict_suffix_of (#a: eqtype) (l1: list a) (m: a) (l2: list a)
: Lemma
  (requires True)
  (ensures ((mem m l1 /\ strict_suffix_of l1 l2) ==> mem m l2))

(*| If `l1` is a strict suffix of `l2`, then `l2` is `append l3 l1` for some
    `l3`. *)
val strict_suffix_of_exists_append
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (ensures (strict_suffix_of l1 l2 ==> (exists l3 . l2 == append l3 l1)))

(*| If `l1` is a strict suffix of `l2` or equal to it, then `l2` is
    `append l3 l1` for some `l3`. *)
val strict_suffix_of_or_eq_exists_append
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (ensures ((strict_suffix_of l1 l2 \/ l1 == l2) ==> (exists l3 . l2 == append l3 l1)))

(** Properties of << with lists *)

(*| The tail of a nonempty list precedes it in the well-founded order `<<`. *)
val precedes_tl
  (#a: Type)
  (l: list a {Cons? l})
: Lemma (ensures (tl l << l))

(*| An element of a list precedes the list in the well-founded order `<<`,
    stated for a list of the form `append l1 (x :: l2)`.

    Triggered automatically on `x << append l1 (x :: l2)`. *)
val precedes_append_cons_r
  (#a: Type)
  (l1: list a)
  (x: a)
  (l2: list a)
: Lemma
  (requires True)
  (ensures (x << append l1 (x :: l2)))
  [SMTPat (x << append l1 (x :: l2))]

(*| Both components of a pair in an association list precede the list in the
    well-founded order `<<`, stated for a list of the form
    `append l1 ((x, y) :: l2)`. *)
val precedes_append_cons_prod_r
  (#a #b: Type)
  (l1: list (a & b))
  (x: a)
  (y: b)
  (l2: list (a & b))
: Lemma
  (ensures
    x << (append l1 ((x, y) :: l2)) /\
    y << (append l1 ((x, y) :: l2)))

(*| Every member of a list precedes the list in the well-founded order `<<`.

    Useful to justify termination of a recursive call on a member. *)
val memP_precedes
  (#a: Type)
  (x: a)
  (l: list a)
: Lemma
  (requires True)
  (ensures (memP x l ==> x << l))

(*| If `FStar.List.Tot.Base.assoc x l` returns `Some y`, then both `x` and `y`
    precede `l` in the well-founded order `<<`. *)
val assoc_precedes
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l: list (a & b))
  (y: b)
: Lemma
  (requires (assoc x l == Some y))
  (ensures (x << l /\ y << l))

(** Properties about find *)

(*| If `FStar.List.Tot.Base.find f l` returns `None`, then `f` returns `false`
    on every member of `l`. *)
val find_none
  (#a: Type)
  (f: (a -> Tot bool))
  (l: list a)
  (x: a)
: Lemma
  (requires (find f l == None /\ memP x l))
  (ensures (f x == false))

(** Properties of init and last *)

(*| A nonempty list is its `FStar.List.Tot.Base.init` followed by its
    `FStar.List.Tot.Base.last`: `l == append (init l) [last l]`. *)
val append_init_last (#a: Type) (l: list a { Cons? l }) : Lemma
  (l == append (init l) [last l])

(*| `FStar.List.Tot.Base.init` and `FStar.List.Tot.Base.last` of `append l [x]`
    are `l` and `x`. *)
val init_last_def (#a: Type) (l: list a) (x: a) : Lemma
  (let l' = append l [x] in
  init l' == l /\ last l' == x)

(*| Two nonempty lists with the same `FStar.List.Tot.Base.init` and the same
    `FStar.List.Tot.Base.last` are equal. *)
val init_last_inj (#a: Type) (l1: list a { Cons? l1 } ) (l2: list a { Cons? l2 } ) : Lemma
  (requires (init l1 == init l2 /\ last l1 == last l2))
  (ensures (l1 == l2))

(* Properties of for_all *)

(*| `FStar.List.Tot.Base.for_all f` holds of `s1 @ s2` exactly when it holds of
    both `s1` and `s2`. *)
val for_all_append #a (f: a -> Tot bool) (s1 s2: list a): Lemma
  (ensures for_all f (s1 @ s2) <==> for_all f s1 && for_all f s2)