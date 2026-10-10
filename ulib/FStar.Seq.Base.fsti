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

(* A logical theory of sequences indexed by natural numbers in [0, n) *)
module FStar.Seq.Base
//#set-options "--fuel 0 --ifuel 1"

module List = FStar.List.Tot.Base

(*| The type of finite sequences of elements of type `a`, indexed from 0.

    An abstract logical model: equality of sequences is characterized by
    `FStar.Seq.Base.equal` and `FStar.Seq.Base.lemma_eq_elim`, and most
    properties are available through lemmas with SMT patterns. Higher-level
    operations and lemmas are in `FStar.Seq.Properties`, and the module
    `FStar.Seq` exports both. *)
new val seq ([@@@strictly_positive] a : Type u#a) : Type u#a

(* Destructors *)
(*| Returns the number of elements of a sequence. *)
val length: #a:Type -> seq a -> Tot nat

(*| Returns the elements of a sequence as a list, in order. The list has the
    same length as the sequence.

    `FStar.Seq.Base.seq_of_list` is its inverse. *)
val seq_to_list (#a:Type) (s:seq a) : Tot (l:list a{List.length l == length s})

(*| Returns a sequence with the elements of a list, in order. The sequence has
    the same length as the list.

    `FStar.Seq.Base.seq_to_list` is its inverse. *)
val seq_of_list (#a:Type) (l:list a) : Tot (s:seq a{List.length l == length s})

(*| Returns the element at index `i`, counting from 0.

    The caller must prove `i < length s`. *)
val index:  #a:Type -> s:seq a -> i:nat{i < length s} -> Tot a

(*| Returns a sequence of length `n` whose elements are all `v`. *)
val create: #a:Type -> nat -> a -> Tot (seq a)

private val init_aux (#a:Type) (len:nat) (k:nat{k < len}) (contents:(i:nat { i < len } -> Tot a))
  :Tot (seq a)

(*| Returns a sequence of length `len` whose element at index `i` is
    `contents i`.

    For a ghost function, use `FStar.Seq.Base.init_ghost`.
    `FStar.Seq.Base.init_index` states the content of the result. *)
inline_for_extraction val init: #a:Type -> len:nat -> contents: (i:nat { i < len } -> Tot a) -> Tot (seq a)

private val init_aux_ghost (#a:Type) (len:nat) (k:nat{k < len}) (contents:(i:nat { i < len } -> GTot a))
  : GTot (seq a)

(*| `FStar.Seq.Base.init` for a ghost function `contents`; the result is ghost. *)
inline_for_extraction val init_ghost: #a:Type -> len:nat -> contents: (i:nat { i < len } -> GTot a) -> GTot (seq a)

(*| The sequence of length 0. *)
val empty (#a:Type) : Tot (s:(seq a){length s=0})

(*| Deprecated: the same as `FStar.Seq.Base.empty`. Use that instead. *)
[@@(deprecated "Seq.empty")]
unfold
let createEmpty (#a:Type)
    : Tot (s:(seq a){length s=0})
    = empty #a

(*| A sequence of length 0 is equal to `FStar.Seq.Base.empty`. *)
val lemma_empty (#a:Type) (s:seq a) : Lemma (length s = 0 ==> s == empty #a)

(*| Returns the sequence `s` with the element at index `n` replaced by `v`.

    The caller must prove `n < length s`. The length is unchanged. *)
val upd: #a:Type -> s:seq a -> n:nat{n < length s} -> a ->  Tot (seq a)

(*| Concatenates two sequences: the elements of the first followed by those of
    the second.

    Also written `s1 @| s2`. The length and indexing lemmas
    `FStar.Seq.Base.lemma_len_append`, `FStar.Seq.Base.lemma_index_app1` and
    `FStar.Seq.Base.lemma_index_app2` apply automatically. *)
val append: #a:Type -> seq a -> seq a -> Tot (seq a)

(*| Adds `x` at the front of `s`. Defined as `append (create 1 x) s`. *)
let cons (#a:Type) (x:a) (s:seq a) : Tot (seq a) = append (create 1 x) s

(*| Infix notation for `FStar.Seq.Base.append`. *)
let ( @| ) (#a:Type) (s1:seq a) (s2:seq a) = append s1 s2

(*| Returns the elements of `s` from index `i` up to, but not including, index
    `j`.

    The caller must prove `i <= j` and `j <= length s`. The result has length
    `j - i`, and its element at index `k` is the element of `s` at index
    `i + k`; `FStar.Seq.Base.lemma_len_slice` and
    `FStar.Seq.Base.lemma_index_slice` state this and apply automatically.

    ```fstar
    let middle (s: FStar.Seq.Base.seq int{FStar.Seq.Base.length s = 4})
      : int
      = FStar.Seq.Base.index (FStar.Seq.Base.slice s 1 3) 0
    ``` *)
val slice:  #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Tot (seq a)

(* Lemmas about seq_to_list/seq_of_list *)
(*| Converting a sequence to a list and back gives the original sequence.
    Applied automatically through its SMT pattern. *)
val lemma_seq_of_seq_to_list : #a:Type -> s:seq a ->
  Lemma
  (requires True)
  (ensures seq_of_list (seq_to_list s) == s)
  [SMTPat (seq_of_list (seq_to_list s))]

(*| Converting a list to a sequence and back gives the original list. Applied
    automatically through its SMT pattern. *)
val lemma_seq_to_seq_of_list : #a:Type -> l:list a ->
  Lemma
  (requires True)
  (ensures seq_to_list (seq_of_list l) == l)
  [SMTPat (seq_to_list (seq_of_list l))]

(*| The sequence of `x :: l` is `x` followed by the sequence of `l`. Applied
    automatically through its SMT pattern. *)
val lemma_seq_of_list_cons : #a:Type -> x:a -> l:list a ->
  Lemma
  (requires True)
  (ensures seq_of_list (x::l) == create 1 x @| seq_of_list l)
  [SMTPat (seq_of_list (x::l))]

(*| The list of `cons x s` is `x` followed by the list of `s`. Applied
    automatically through its SMT pattern. *)
val lemma_seq_to_list_cons : #a:Type -> x:a -> s:seq a ->
  Lemma
  (requires True)
  (ensures seq_to_list (cons x s) == x :: seq_to_list s)
  [SMTPat (seq_to_list (cons x s))]

(* Lemmas about length *)
(*| `create n v` has length `n`. Applied automatically through its SMT pattern. *)
val lemma_create_len: #a:Type -> n:nat -> i:a -> Lemma
  (requires True)
  (ensures (length (create n i) = n))
  [SMTPat (length (create n i))]

(*| `init n contents` has length `n`. Applied automatically through its SMT
    pattern. *)
val lemma_init_len: #a:Type -> n:nat -> contents: (i:nat { i < n } -> Tot a) -> Lemma
  (requires True)
  (ensures (length (init n contents) = n))
  [SMTPat (length (init n contents))]

private val lemma_init_aux_len (#a:Type) (n:nat) (k:nat{k < n}) (contents:(i:nat{ i < n } -> Tot a))
  : Lemma (requires True)
    (ensures (length (init_aux n k contents) = n - k))
    [SMTPat (length (init_aux n k contents))]

(*| `init_ghost n contents` has length `n`. Applied automatically through its
    SMT pattern. *)
val lemma_init_ghost_len: #a:Type -> n:nat -> contents: (i:nat { i < n } -> GTot a) -> Lemma
  (requires True)
  (ensures (length (init_ghost n contents) = n))
  [SMTPat (length (init_ghost n contents))]

private val lemma_init_ghost_aux_len (#a:Type) (n:nat) (k:nat{k < n}) (contents:(i:nat{ i < n } -> GTot a))
  : Lemma (requires True)
    (ensures (length (init_aux_ghost n k contents) = n - k))
    [SMTPat (length (init_aux_ghost n k contents))]

(*| `upd s n v` has the same length as `s`. Applied automatically through its
    SMT pattern. *)
val lemma_len_upd: #a:Type -> n:nat -> v:a -> s:seq a{n < length s} -> Lemma
  (requires True)
  (ensures (length (upd s n v) = length s))
  [SMTPat (length (upd s n v))]

(*| The length of `append s1 s2` is the sum of their lengths. Applied
    automatically through its SMT pattern. *)
val lemma_len_append: #a:Type -> s1:seq a -> s2:seq a -> Lemma
  (requires True)
  (ensures (length (append s1 s2) = length s1 + length s2))
  [SMTPat (length (append s1 s2))]

(*| `slice s i j` has length `j - i`. Applied automatically through its SMT
    pattern. *)
val lemma_len_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Lemma
  (requires True)
  (ensures (length (slice s i j) = j - i))
  [SMTPat (length (slice s i j))]

(* Lemmas about index *)
(*| Every element of `create n v` is `v`. Applied automatically through its
    SMT pattern. *)
val lemma_index_create: #a:Type -> n:nat -> v:a -> i:nat{i < n} -> Lemma
  (requires True)
  (ensures (index (create n v) i == v))
  [SMTPat (index (create n v) i)]

(*| After `upd s n v`, the element at index `n` is `v`. Applied automatically
    through its SMT pattern. *)
val lemma_index_upd1: #a:Type -> s:seq a -> n:nat{n < length s} -> v:a -> Lemma
  (requires True)
  (ensures (index (upd s n v) n == v))
  [SMTPat (index (upd s n v) n)]

(*| `upd s n v` leaves the elements at indices other than `n` unchanged.
    Applied automatically through its SMT pattern. *)
val lemma_index_upd2: #a:Type -> s:seq a -> n:nat{n < length s} -> v:a -> i:nat{i<>n /\ i < length s} -> Lemma
  (requires True)
  (ensures (index (upd s n v) i == index s i))
  [SMTPat (index (upd s n v) i)]

(*| For an index within `s1`, `append s1 s2` has the element of `s1`. Applied
    automatically through its SMT pattern. *)
val lemma_index_app1: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1} -> Lemma
  (requires True)
  (ensures (index (append s1 s2) i == index s1 i))
  [SMTPat (index (append s1 s2) i)]

(*| For an index `i` past the end of `s1`, `append s1 s2` has the element of
    `s2` at index `i - length s1`. Applied automatically through its SMT
    pattern. *)
val lemma_index_app2: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1 + length s2 /\ length s1 <= i} -> Lemma
  (requires True)
  (ensures (index (append s1 s2) i == index s2 (i - length s1)))
  [SMTPat (index (append s1 s2) i)]

(*| The element of `slice s i j` at index `k` is the element of `s` at index
    `k + i`. Applied automatically through its SMT pattern. *)
val lemma_index_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s} -> k:nat{k < j - i} -> Lemma
  (requires True)
  (ensures (index (slice s i j) k == index s (k + i)))
  [SMTPat (index (slice s i j) k)]

(*| If `a` supports decidable equality, so does `seq a`. Applied automatically
    through its SMT pattern. *)
val hasEq_lemma: a:Type -> Lemma (requires (hasEq a)) (ensures (hasEq (seq a))) [SMTPat (hasEq  (seq a))]

(*| Extensional equality of sequences: the same length and the same element
    at every index.

    `FStar.Seq.Base.lemma_eq_intro` proves it from the elements, and
    `FStar.Seq.Base.lemma_eq_elim` turns it into provable equality `==`. To
    show two sequences equal, it is usually enough to assert `equal s1 s2`. *)
[@@ remove_unused_type_parameters [0; 1; 2]]
val equal (#a:Type) (s1:seq a) (s2:seq a) : Tot prop

(* decidable equality *)
private val eq_i:
  #a:eqtype -> s1:seq a -> s2:seq a{length s1 = length s2}
  -> i:nat{i <= length s1}
  -> Tot (r:bool{r <==> (forall j. (j >= i /\ j < length s1) ==> (index s1 j = index s2 j))})

(*| Decides `FStar.Seq.Base.equal` for sequences over an `eqtype`; the result
    is `true` exactly when the two sequences are equal. *)
val eq: #a:eqtype -> s1:seq a -> s2:seq a -> Tot (r:bool{r <==> equal s1 s2})

(*| Two sequences with the same length and the same element at every index
    are `FStar.Seq.Base.equal`. Applied automatically through its SMT pattern. *)
val lemma_eq_intro: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (length s1 = length s2
               /\ (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} (index s1 i == index s2 i))))
     (ensures (equal s1 s2))
     [SMTPat (equal s1 s2)]

(*| Equal sequences are `FStar.Seq.Base.equal`. Applied automatically through
    its SMT pattern. *)
val lemma_eq_refl: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (s1 == s2))
     (ensures (equal s1 s2))
     [SMTPat (equal s1 s2)]

(*| Sequences that are `FStar.Seq.Base.equal` are equal. Applied automatically
    through its SMT pattern; together with
    `FStar.Seq.Base.lemma_eq_intro` it gives extensionality. *)
val lemma_eq_elim: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (equal s1 s2))
     (ensures (s1==s2))
     [SMTPat (equal s1 s2)]

(* Properties of [append] *)

(*| `FStar.Seq.Base.append` is associative.

    Has no SMT pattern; call it where needed. *)
val append_assoc
  (#a: Type)
  (s1 s2 s3: seq a)
: Lemma
  (ensures (append (append s1 s2) s3 == append s1 (append s2 s3)))

(*| Appending a sequence to `FStar.Seq.Base.empty` gives the sequence.

    Has no SMT pattern; call it where needed. *)
val append_empty_l
  (#a: Type)
  (s: seq a)
: Lemma
  (ensures (append empty s == s))

(*| Appending `FStar.Seq.Base.empty` to a sequence gives the sequence.

    Has no SMT pattern; call it where needed. *)
val append_empty_r
  (#a: Type)
  (s: seq a)
: Lemma
  (ensures (append s empty == s))


(*| The element of `init len contents` at every index `i` is `contents i`.

    Has no SMT pattern; `FStar.Seq.Base.init_index_` states the same for one
    index and applies automatically. *)
val init_index (#a:Type) (len:nat) (contents:(i:nat { i < len } -> Tot a))
  : Lemma (requires True)
    (ensures (forall (i:nat{i < len}). index (init len contents) i == contents i))

(*| The element of `init len contents` at index `j` is `contents j`. Applied
    automatically through its SMT pattern. *)
val init_index_ (#a:Type) (len:nat) (contents:(i:nat { i < len } -> Tot a)) (j: nat)
  : Lemma (requires j < len)
    (ensures (index (init len contents) j == contents j))
    [SMTPat (index (init len contents) j)]

(*| The element of `init_ghost len contents` at every index `i` is
    `contents i`.

    Has no SMT pattern; `FStar.Seq.Base.init_ghost_index_` states the same for
    one index and applies automatically. *)
val init_ghost_index (#a:Type) (len:nat) (contents:(i:nat { i < len } -> GTot a))
  : Lemma (requires True)
    (ensures (forall (i:nat{i < len}). index (init_ghost len contents) i == contents i))

(*| The element of `init_ghost len contents` at index `j` is `contents j`.
    Applied automatically through its SMT pattern. *)
val init_ghost_index_ (#a:Type) (len:nat) (contents:(i:nat { i < len } -> GTot a)) (j: nat)
  : Lemma (requires j < len)
    (ensures (index (init_ghost len contents) j == contents j))
    [SMTPat (index (init_ghost len contents) j)]

(*| Sequences that are heterogeneously equal, `s1 === s2`, have the same
    element type. *)
val lemma_equal_instances_implies_equal_types (_:unit)
  :Lemma (forall (a:Type u#a) (b:Type u#a) (s1:seq a) (s2:seq b). s1 === s2 ==> a == b)
