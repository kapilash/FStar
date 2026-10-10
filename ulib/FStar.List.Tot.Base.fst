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
This module defines all pure and total operations on lists that can be
used in specifications. It is implemented by FStar_List_Tot_Base.ml, any
functional change and/or the addition of new functions MUST be reflected
there.

@summary Pure total operations on lists
*)
module FStar.List.Tot.Base

(**
Base operations
*)

(*| Returns `true` exactly when the list is empty. *)
val isEmpty: list 'a -> Tot bool
let isEmpty l = match l with
  | [] -> true
  | _ -> false

(*| Returns the first element of a nonempty list.

    The refinement `Cons? l` must be proved by the caller. Named as in OCaml,
    F# and Coq. For a list that may be empty, match on it instead. *)
val hd: l:list 'a{Cons? l} -> Tot 'a
let hd = function
  | hd::_ -> hd

(*| Returns a nonempty list without its first element.

    The same function as `FStar.List.Tot.Base.tl`; the refinement `Cons? l`
    must be proved by the caller. *)
val tail: l:list 'a {Cons? l} -> Tot (list 'a)
let tail = function
  | _::tl -> tl

(*| Returns a nonempty list without its first element.

    Named as in OCaml, F# and Coq. The same function as
    `FStar.List.Tot.Base.tail`. *)
val tl: l:list 'a {Cons? l} -> Tot (list 'a)
let tl = tail

(*| Returns the last element of a nonempty list. Named as in Haskell. *)
val last: l:list 'a {Cons? l} -> Tot 'a
let rec last = function
  | [hd] -> hd
  | _::tl -> last tl

(*| Returns a nonempty list without its last element. Named as in Haskell.

    Together with `FStar.List.Tot.Base.last` it splits off the end of a list;
    `FStar.List.Tot.Base.unsnoc` returns both parts at once. *)
val init: l:list 'a {Cons? l} -> Tot (list 'a)
let rec init = function
  | [_] -> []
  | hd::tl -> hd::(init tl)

(*| Returns the number of elements of a list.

    Lemmas relating `length` to the other operations are in
    `FStar.List.Tot.Properties`. *)
val length: list 'a -> Tot nat
let rec length = function
  | [] -> 0
  | _::tl -> 1 + length tl

(*| Returns `Some` of the element at index `n`, counting from 0, or `None` if
    the list has no such element.

    The total, unrefined counterpart of `FStar.List.Tot.Base.index`. *)
val nth: list 'a -> nat -> Tot (option 'a)
let rec nth l n = match l with
  | []     -> None
  | hd::tl -> if n = 0 then Some hd else nth tl (n - 1)

(*| Returns the element at index `i`, counting from 0.

    The caller must prove `i < length l`. For an index that may be out of
    range, use `FStar.List.Tot.Base.nth`.

    ```fstar
    let third : int = FStar.List.Tot.Base.index [10; 20; 30] 2
    ``` *)
val index: #a:Type -> l:list a -> i:nat{i < length l} -> Tot a (decreases i)
let rec index #a (l: list a) (i:nat{i < length l}): Tot a =
  if i = 0 then
    hd l
  else
    index (tl l) (i - 1)

(*| Returns the number of occurrences of `x` in a list, using decidable
    equality. Similar to `List.count_occ` in Coq. *)
val count: #a:eqtype -> a -> list a -> Tot nat
let rec count #a x = function
  | [] -> 0
  | hd::tl -> if x=hd then 1 + count x tl else count x tl

(*| Prepends the elements of the first list, in reverse order, to the second
    list.

    `rev_acc l1 l2` equals `append (rev l1) l2` and is tail recursive. Similar
    to `List.rev_append` in OCaml and Coq. *)
val rev_acc: list 'a -> list 'a -> Tot (list 'a)
let rec rev_acc l acc = match l with
    | [] -> acc
    | hd::tl -> rev_acc tl (hd::acc)

(*| Returns the elements of a list in reverse order.

    Defined with `FStar.List.Tot.Base.rev_acc`. Lemmas about it, such as
    `FStar.List.Tot.Properties.rev_involutive`, are in
    `FStar.List.Tot.Properties`. *)
val rev: list 'a -> Tot (list 'a)
let rev l = rev_acc l []

(*| Concatenates two lists: the elements of `l1` followed by those of `l2`.

    Also written `l1 @ l2`. Named as in OCaml and F#; `List.app` in Coq. *)
val append: list 'a -> list 'a -> Tot (list 'a)
let rec append x y = match x with
  | [] -> y
  | a::tl -> a::append tl y

(*| Infix notation for `FStar.List.Tot.Base.append`, as in OCaml and F#. *)
let ( @ ) x y = append x y

(*| Adds `x` to the end of `l`, taking the pair `(l, x)`.

    The pair argument is intentional. With two separate arguments, the SMT
    pattern of `FStar.List.Tot.Properties.lemma_unsnoc_snoc`, which connects `snoc` and
    `FStar.List.Tot.Base.unsnoc`, would either be too restrictive or trigger
    too often. See [FStar pull request 1560](https://github.com/FStarLang/FStar/pull/1560)
    for the discussion. *)
val snoc: (list 'a & 'a) -> Tot (list 'a)
let snoc (l, x) = append l [x]

(*| Concatenates a list of lists, keeping the elements in order. Named as in
    OCaml and Coq. *)
val flatten: list (list 'a) -> Tot (list 'a)
let rec flatten l = match l with
    | [] -> []
    | hd::tl -> append hd (flatten tl)

(*| Applies a total function to each element of a list, keeping the order.
    Named as in OCaml, Coq and F#.

    For a ghost function, use `FStar.List.Tot.Base.map_gtot`. *)
val map: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

(*| Like `FStar.List.Tot.Base.mapi`, but numbering the elements from `i`
    instead of 0: the element at position `k` is mapped to `f (i + k) x`. *)
val mapi_init: (int -> 'a -> Tot 'b) -> list 'a -> int -> Tot (list 'b)
let rec mapi_init f l i = match l with
    | [] -> []
    | hd::tl -> (f i hd)::(mapi_init f tl (i+1))

(*| Applies `f k x` to the element `x` at each position `k`, counting from 0,
    keeping the order. Named as in OCaml. *)
val mapi: (int -> 'a -> Tot 'b) -> list 'a -> Tot (list 'b)
let mapi f l = mapi_init f l 0

(*| Applies `f` to each element and concatenates the resulting lists.

    Equal to `flatten (map f l)`, and computes the same list as
    `FStar.List.Tot.Base.collect`. *)
val concatMap: ('a -> Tot (list 'b)) -> list 'a -> Tot (list 'b)
let rec concatMap f = function
  | [] -> []
  | a::tl ->
    let fa = f a in
    let ftl = concatMap f tl in
    append fa ftl

(*| Combines the elements from the left with an accumulator.

    `fold_left f x [y1; y2; y3]` is `f (f (f x y1) y2) y3`. Tail recursive.
    Named as in OCaml and Coq. *)
val fold_left: ('a -> 'b -> Tot 'a) -> 'a -> l:list 'b -> Tot 'a (decreases l)
let rec fold_left f x l = match l with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

(*| Combines the elements from the right with an accumulator.

    `fold_right f [x1; x2; x3] y` is `f x1 (f x2 (f x3 y))`. Named as in OCaml
    and Coq. For a ghost function, use `FStar.List.Tot.Base.fold_right_gtot`. *)
val fold_right: ('a -> 'b -> Tot 'b) -> list 'a -> 'b -> Tot 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

(*| `FStar.List.Tot.Base.fold_right` for a ghost function `f`, with the list
    as the first argument. *)
let rec fold_right_gtot (#a:Type) (#b:Type) (l:list a) (f:a -> b -> GTot b) (x:b)
  : GTot b
  = match l with
    | [] -> x
    | hd::tl -> f hd (fold_right_gtot tl f x)

(* We define map in terms of fold, to share simple lemmas *)
(*| `FStar.List.Tot.Base.map` for a ghost function `f`.

    Defined with `FStar.List.Tot.Base.fold_right_gtot`, so that lemmas about
    folds also apply to it. *)
let map_gtot #a #b (f:a -> GTot b) (x:list a)
  : GTot (list b)
  = fold_right_gtot x (fun x tl -> f x :: tl) []

(*| Folds from the left over two lists of the same length at once.

    `fold_left2 f a [y1; y2] [z1; z2]` is `f (f a y1 z1) y2 z2`. The caller
    must prove `length l1 == length l2`. Named as in OCaml. *)
val fold_left2 : f:('a -> 'b -> 'c -> Tot 'a) -> accu:'a -> l1:(list 'b) -> l2:(list 'c) ->
  Pure 'a (requires (length l1 == length l2)) (ensures (fun _ -> True)) (decreases l1)
let rec fold_left2 f accu l1 l2 =
  match (l1, l2) with
  | ([], []) -> accu
  | (a1::l1, a2::l2) -> fold_left2 f (f accu a1 a2) l1 l2

(*| The proposition that `x` is an element of `l`.

    Does not need decidable equality, so it works at any type and in
    specifications. The boolean counterpart for an `eqtype` is
    `FStar.List.Tot.Base.mem`; `FStar.List.Tot.Properties.mem_memP` relates
    the two. Similar to `List.In` in Coq. *)
let rec memP (#a: Type) (x: a) (l: list a) : prop =
  match l with
  | [] -> False
  | y :: q -> x == y \/ memP x q

(** List searching **)

(*| Returns `true` exactly when `x` is an element of the list, using decidable
    equality. Named as in OCaml.

    For a type without decidable equality, use the proposition
    `FStar.List.Tot.Base.memP`. *)
val mem: #a:eqtype -> a -> list a -> Tot bool
let rec mem #a x = function
  | [] -> false
  | hd::tl -> if hd = x then true else mem x tl

(*| The same function as `FStar.List.Tot.Base.mem`. *)
let contains : #a:eqtype -> a -> list a -> Tot bool = mem

(*| Returns `true` exactly when `f` holds for some element of the list. *)
val existsb: #a:Type
       -> f:(a -> Tot bool)
       -> list a
       -> Tot bool
let rec existsb #a f l = match l with
 | [] -> false
 | hd::tl -> if f hd then true else existsb f tl

(*| Returns the first element for which `f` holds, or `None` if there is none.

    The result's type records that `f` holds for the element found. Use
    `FStar.List.Tot.Base.tryFind` when that refinement is not wanted. *)
val find: #a:Type
        -> f:(a -> Tot bool)
        -> list a
        -> Tot (option (x:a{f x}))
let rec find #a f l = match l with
  | [] -> None #(x:a{f x}) //These type annotations are only present because it makes bootstrapping go much faster
  | hd::tl -> if f hd then Some #(x:a{f x}) hd else find f tl

(** Filtering elements of a list [l] through a Boolean pure total
predicate [f] *)

(*| Keeps the elements for which `f` holds, in their original order. Named as
    in OCaml and Coq.

    `FStar.List.Tot.Base.mem_filter_forall` characterizes the result and is
    applied automatically through its SMT pattern. *)
val filter : #a: Type -> f:(a -> Tot bool) -> l: list a -> Tot (list a)
let rec filter #a f = function
  | [] -> []
  | hd::tl -> if f hd then hd::filter f tl else filter f tl

(*| An element is in `filter f l` exactly when it is in `l` and `f` holds for
    it, for one given element `x`. *)
let rec mem_filter (#a: Type) (f: (a -> Tot bool)) (l: list a) (x: a)
    : Lemma (memP x (filter f l) <==> memP x l /\ f x) =
  match l with
  | [] -> ()
  | hd :: tl -> mem_filter f tl x

(*| For every `x`, `x` is in `filter f l` exactly when it is in `l` and `f x`
    holds.

    Has an SMT pattern on `filter f l`, so it rarely needs to be called. *)
let mem_filter_forall (#a: Type) (f: (a -> Tot bool)) (l: list a)
    : Lemma (forall x. memP x (filter f l) <==> memP x l /\ f x)
            [SMTPat (filter f l)] =
  introduce forall x . memP x (filter f l) <==> memP x l /\ f x
  with mem_filter f l x

(*| Returns `true` exactly when `f` holds for every element of the list. Named
    as in OCaml; `List.forallb` in Coq.

    `FStar.List.Tot.Base.for_all_mem` relates it to membership. *)
val for_all: ('a -> Tot bool) -> list 'a -> Tot bool
let rec for_all f l = match l with
    | [] -> true
    | hd::tl -> if f hd then for_all f tl else false

(*| `for_all f l` holds exactly when `f x` holds for every member `x` of `l`. *)
let rec for_all_mem
  (#a: Type)
  (f: (a -> Tot bool))
  (l: list a)
: Lemma
  (for_all f l <==> (forall x . memP x l ==> f x))
= match l with
  | [] -> ()
  | _ :: q -> for_all_mem f q

(*| The proposition that `pre` holds for every element of the list.

    The propositional counterpart of `FStar.List.Tot.Base.for_all`;
    `FStar.List.Tot.Base.for_allP_eq` relates it to membership. *)
val for_allP: #a:Type -> (a -> prop) -> list a -> prop
let rec for_allP #a pre l =
  match l with
  | [] -> True
  | h::t -> pre h /\ for_allP pre t

(*| `for_allP pre l` holds exactly when `pre x` holds for every member `x` of
    `l`. *)
val for_allP_eq:
  #a:Type ->
  pre:(a -> prop) -> l:list a ->
  Lemma (for_allP pre l <==> (forall x. memP x l ==> pre x))
let rec for_allP_eq #a pre l =
  match l with
  | [] -> ()
  | h::t -> for_allP_eq pre t

(*| Applies `f` to each element and concatenates the resulting lists.

    Computes the same list as `FStar.List.Tot.Base.concatMap`, and equals
    `flatten (map f l)`. *)
val collect: ('a -> Tot (list 'b)) -> list 'a -> Tot (list 'b)
let rec collect f l = match l with
    | [] -> []
    | hd::tl -> append (f hd) (collect f tl)

(*| Returns the first element for which `p` holds, or `None` if there is none.

    Unlike `FStar.List.Tot.Base.find`, the result is not refined by `p`. *)
val tryFind: ('a -> Tot bool) -> list 'a -> Tot (option 'a)
let rec tryFind p l = match l with
    | [] -> None
    | hd::tl -> if p hd then Some hd else tryFind p tl

(*| Returns the first `Some` result of `f` over the elements, in order, or
    `None` if `f` returns `None` for every element. *)
val tryPick: ('a -> Tot (option 'b)) -> list 'a -> Tot (option 'b)
let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl

(*| Applies `f` to each element and keeps the values `y` for which it returns
    `Some y`, in order. *)
val choose: ('a -> Tot (option 'b)) -> list 'a -> Tot (list 'b)
let rec choose f l = match l with
    | [] -> []
    | hd::tl ->
       match f hd with
         | Some x -> x::(choose f tl)
         | None -> choose f tl

(*| Splits a list into the elements for which `f` holds and those for which
    it does not, both in their original order.

    `FStar.List.Tot.Base.partition_length` states that no element is lost. *)
val partition: f:('a -> Tot bool) -> list 'a -> Tot (list 'a & list 'a)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partition f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2

(*| Returns `true` exactly when every element of `la` is also an element of
    `lb`, using decidable equality. *)
val subset: #a:eqtype -> list a -> list a -> Tot bool
let rec subset #a la lb =
  match la with
  | [] -> true
  | h :: tl ->  mem h lb && subset tl lb

(*| Returns `true` exactly when no element occurs more than once in the list,
    using decidable equality.

    The propositional counterpart is `FStar.List.Tot.Base.no_repeats_p`. *)
val noRepeats : #a:eqtype -> list a -> Tot bool
let rec noRepeats #a la =
  match la with
  | [] -> true
  | h :: tl -> not(mem h tl) && noRepeats tl


(*| The proposition that no element occurs more than once in the list.

    Does not need decidable equality. The boolean counterpart is
    `FStar.List.Tot.Base.noRepeats`. *)
val no_repeats_p : #a:Type -> list a -> Tot prop
let rec no_repeats_p #a la =
  match la with
  | [] -> True
  | h :: tl -> ~(memP h tl) /\ no_repeats_p tl

(** List of tuples **)

(*| Looks up a key in an association list: returns `Some y` for the first pair
    `(x, y)` whose key is `x`, or `None` if there is no such pair. Named as in
    OCaml. *)
val assoc: #a:eqtype -> #b:Type -> a -> list (a & b) -> Tot (option b)
let rec assoc #a #b x = function
  | [] -> None
  | (x', y)::tl -> if x=x' then Some y else assoc x tl

(*| Turns a list of pairs into a pair of lists: the first components and the
    second components, in order. Named as in OCaml.

    Also available as `FStar.List.Tot.Base.unzip`. *)
val split: list ('a & 'b) -> Tot (list 'a & list 'b)
let rec split l = match l with
    | [] -> ([],[])
    | (hd1,hd2)::tl ->
       let (tl1,tl2) = split tl in
       (hd1::tl1,hd2::tl2)

(*| Turns a list of pairs into a pair of lists. The same function as
    `FStar.List.Tot.Base.split`; named as in Haskell. *)
let unzip l = split l

(*| Turns a list of triples into a triple of lists, in order. Named as in
    Haskell. *)
val unzip3: list ('a & 'b & 'c) -> Tot (list 'a & list 'b & list 'c)
let rec unzip3 l = match l with
    | [] -> ([],[],[])
    | (hd1,hd2,hd3)::tl ->
       let (tl1,tl2,tl3) = unzip3 tl in
       (hd1::tl1,hd2::tl2,hd3::tl3)

(** Splitting a list at some index **)

(*| Splits a list after its first `n` elements.

    Returns the prefix of length `n`, or the whole list if it is shorter, and
    the remaining elements. `FStar.List.Tot.Base.lemma_splitAt_snd_length`
    gives the length of the second part. *)
let rec splitAt (#a:Type) (n:nat) (l:list a) : Tot (list a & list a) =
  if n = 0 then [], l
  else
    match l with
    | [] -> [], l
    | x :: xs -> let l1, l2 = splitAt (n-1) xs in x :: l1, l2

(*| When `n <= length l`, the second part of `splitAt n l` has length
    `length l - n`. *)
let rec lemma_splitAt_snd_length (#a:Type) (n:nat) (l:list a) :
  Lemma
    (requires (n <= length l))
    (ensures (length (snd (splitAt n l)) = length l - n)) =
  match n, l with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> lemma_splitAt_snd_length (n - 1) l'

(*| Splits a nonempty list into all elements but the last, and the last
    element.

    The inverse of `FStar.List.Tot.Base.snoc`; the lemmas connecting the two
    are in `FStar.List.Tot.Properties`. *)
val unsnoc: #a:Type -> l:list a{length l > 0} -> Tot (list a & a)
let unsnoc #a l =
  let l1, l2 = splitAt (length l - 1) l in
  lemma_splitAt_snd_length (length l - 1) l;
  l1, hd l2

(*| Splits a list around the element at index `i`: the elements before it,
    the element itself, and the elements after it.

    The caller must prove `i < length l`. *)
val split3: #a:Type -> l:list a -> i:nat{i < length l} -> Tot (list a & a & list a)
let split3 #a l i =
  let a, rest = splitAt i l in
  lemma_splitAt_snd_length i l;
  let b :: c = rest in
  a, b, c

(** Sorting (implemented as quicksort) **)

(*| The two lists returned by `partition f l` have lengths that add up to
    `length l`. *)
val partition_length: f:('a -> Tot bool)
                    -> l:list 'a
                    -> Lemma (requires True)
                            (ensures (length (fst (partition f l))
                                      + length (snd (partition f l)) = length l))
let rec partition_length f l = match l with
  | [] -> ()
  | hd::tl -> partition_length f tl

(*| Turns a comparison function into a strict order: `bool_of_compare f x y`
    holds exactly when `f x y < 0`.

    Comparison functions follow the OCaml and F# convention: negative when
    the first argument comes first. `FStar.List.Tot.Base.sortWith` uses this
    to sort in ascending order. *)
val bool_of_compare : #a:Type -> (a -> a -> Tot int) -> a -> a -> Tot bool
let bool_of_compare #a f x y = f x y < 0

(*| Turns a strict order `rel` into a comparison function.

    `compare_of_bool rel x y` is `-1` when `rel x y` holds, `0` when `x = y`,
    and `1` otherwise. `FStar.List.Tot.Base.compare_of_bool_of_compare` states
    that `FStar.List.Tot.Base.bool_of_compare` recovers `rel`. *)
val compare_of_bool : #a:eqtype -> (a -> a -> Tot bool) -> a -> a -> Tot int
let compare_of_bool #a rel x y =
    if x `rel` y  then -1
    else if x = y then 0
    else 1

(*| Converting a strict order with `FStar.List.Tot.Base.compare_of_bool` and
    back with `FStar.List.Tot.Base.bool_of_compare` gives the original order. *)
let compare_of_bool_of_compare (#a:eqtype) (f:a -> a -> Tot bool)
  : Lemma (forall x y. bool_of_compare (compare_of_bool f) x y == f x y)
  = ()

(*| Sorts a list in ascending order according to a comparison function.

    If `f x y < 0`, `x` comes before `y` in the result. Implemented as
    quicksort. Lemmas about the result, such as
    `FStar.List.Tot.Properties.sortWith_permutation`, are in
    `FStar.List.Tot.Properties`. *)
val sortWith: ('a -> 'a -> Tot int) -> l:list 'a -> Tot (list 'a) (decreases (length l))
let rec sortWith f = function
  | [] -> []
  | pivot::tl ->
     let hi, lo = partition (bool_of_compare f pivot) tl in
     partition_length (bool_of_compare f pivot) tl;
     append (sortWith f lo) (pivot::sortWith f hi)

(*| The proposition that `l1` is a strict suffix of `l2`: `l1` is obtained by
    removing at least one element from the front of `l2`. *)
let rec strict_suffix_of (#a: Type) (l1 l2: list a)
: Pure prop
  (requires True)
  (ensures (fun _ -> True))
  (decreases l2)
= match l2 with
  | [] -> False
  | _ :: q -> l1 == q \/ l1 `strict_suffix_of` q

(*| Deprecated: a misnamed alias of `FStar.List.Tot.Base.strict_suffix_of`.
    Use that instead. *)
[@@deprecated "This function was misnamed: Please use 'strict_suffix_of'"]
let strict_prefix_of = strict_suffix_of

(*| Forgets the refinement on the elements of a list, keeping the elements
    and their order. *)
val list_unref : #a:Type -> #p:(a -> prop) -> list (x:a{p x}) -> Tot (list a)
let rec list_unref #a #p l =
    match l with
    | [] -> []
    | x::xs -> x :: list_unref xs

(*| Refines each element of a list by a boolean predicate `p` that the caller
    has proved, with `for_all p l`, to hold for every element.

    The result has the same length and the same elements as the input. *)
val list_refb: #a:eqtype -> #p:(a -> Tot bool) ->
  l:list a { for_all p l } ->
  Tot (l':list (x:a{ p x }) {
    length l = length l' /\
    (forall i. {:pattern (index l i) } index l i = index l' i) })
let rec list_refb #a #p l =
  match l with
  | hd :: tl -> hd :: list_refb #a #p tl
  | [] -> []

(*| Refines each element of a list by a predicate `p` that the caller has
    proved to hold for every member.

    The result has the same length and the same elements as the input. For a
    boolean predicate, `FStar.List.Tot.Base.list_refb` takes the precondition
    as `for_all p l` instead. *)
val list_ref: #a:eqtype -> #p:(a -> Tot prop) -> l:list a {
  forall x. {:pattern mem x l} mem x l ==> p x
} -> Tot (l':list (x:a{ p x }) {
    length l = length l' /\
    (forall i. {:pattern (index l i) } index l i = index l' i) })
let rec list_ref #a #p l =
  match l with
  | hd :: tl ->
      assert (mem hd l);
      assert (p hd);
      assert (forall x. {:pattern mem x tl} mem x tl ==> mem x l);
      hd :: list_ref #a #p tl
  | [] -> []
