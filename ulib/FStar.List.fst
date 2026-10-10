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
F* standard library List module. 

@summary F* stdlib List module. 
*)
module FStar.List
open FStar.All
include FStar.List.Tot

(** Base operations **)

(*| Returns the first element of a list, in the `ML` effect; fails with an
    exception on the empty list.

    This hides `FStar.List.Tot.Base.hd`, which instead requires a proof that
    the list is nonempty. Named as in OCaml, F# and Coq.

    ```fstar
    let sum_of_heads (l1 l2: list int) : ML int =
      FStar.List.hd l1 + FStar.List.hd l2
    ``` *)
val hd: list 'a -> ML 'a
let hd = function
  | hd::tl -> hd
  | _ -> failwith "head of empty list"

(*| Returns a list without its first element, in the `ML` effect; fails with an
    exception on the empty list.

    This hides `FStar.List.Tot.Base.tail`, which instead requires a proof that
    the list is nonempty. The same function as `FStar.List.tl`. *)
val tail: list 'a -> ML (list 'a)
let tail = function
  | hd::tl -> tl
  | _ -> failwith "tail of empty list"

(*| Returns a list without its first element, in the `ML` effect; fails with an
    exception on the empty list.

    This hides `FStar.List.Tot.Base.tl`. The same function as `FStar.List.tail`.
    Named as in OCaml, F# and Coq. *)
val tl : list 'a -> ML (list 'a)
let tl l = tail l

(*| Returns the last element of a list, in the `ML` effect; fails with an
    exception on the empty list.

    This hides `FStar.List.Tot.Base.last`, which instead requires a proof that
    the list is nonempty. Named as in Haskell. *)
val last: list 'a -> ML 'a
let rec last = function
  | [hd] -> hd
  | _::tl -> last tl
  | _ -> failwith "last of empty list"

(*| Returns a list without its last element, in the `ML` effect; fails with an
    exception on the empty list.

    This hides `FStar.List.Tot.Base.init`, which instead requires a proof that
    the list is nonempty. Named as in Haskell. *)
val init: list 'a -> ML (list 'a)
let rec init = function
  | [_] -> []
  | hd::tl -> hd::(init tl)
  | _ -> failwith "init of empty list"

(*| Returns the element at index `n`, counting from 0, in the `ML` effect.

    Fails with an exception if `n` is negative or the list has at most `n`
    elements. This hides `FStar.List.Tot.Base.nth`, which returns an `option`
    instead; `FStar.List.Tot.Base.index` is the total variant with a bound
    proved by the caller. *)
val nth: list 'a -> int -> ML 'a
let rec nth l n =
  if n < 0 then
    failwith "nth takes a non-negative integer as input"
  else
    if n = 0 then
      match l with
        | [] -> failwith "not enough elements"
        | hd::_ -> hd
    else
      match l with
        | [] -> failwith "not enough elements"
        | _::tl -> nth tl (n - 1)

(** Iterators **)

(*| Applies the effectful function `f` to each element of the list, from first
    to last, for its effects. Named as in OCaml and F#. *)
val iter: ('a -> ML unit) -> list 'a -> ML unit
let rec iter f x = match x with
  | [] -> ()
  | a::tl -> let _ = f a in iter f tl

(*| Helper for `FStar.List.iteri`: calls `f (n + k) x` on the element `x` at
    index `k` of the list, from first to last, where `n` is the first argument. *)
val iteri_aux: int -> (int -> 'a -> ML unit) -> list 'a -> ML unit
let rec iteri_aux i f x = match x with
  | [] -> ()
  | a::tl -> f i a; iteri_aux (i+1) f tl

(*| Applies `f k x` to each element `x` of the list and its index `k`, counting
    from 0, from first to last, for its effects. Named as in OCaml. *)
val iteri: (int -> 'a -> ML unit) -> list 'a -> ML unit
let iteri f x = iteri_aux 0 f x

(*| Applies the effectful function `f` to each element of the list, from first
    to last, and returns the list of results.

    This hides `FStar.List.Tot.Base.map`, which requires `f` to be total; that
    version is still available as `FStar.List.mapT`. Named as in OCaml, Coq and
    F#. *)
val map: ('a -> ML 'b) -> list 'a -> ML (list 'b)
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

(*| Applies a total function to each element of a list and returns the list of
    results.

    The same function as `FStar.List.Tot.Base.map`, kept under this name
    because `FStar.List.map` hides it with an `ML` variant. *)
val mapT: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let mapT = FStar.List.Tot.map

(*| Helper for `FStar.List.mapi`: applies `f (i + k)` to the element at index
    `k` of the list, from first to last, where `i` is the last argument, and
    returns the list of results in the `ML` effect.

    This hides `FStar.List.Tot.Base.mapi_init`, which requires `f` to be total. *)
val mapi_init: (int -> 'a -> ML 'b) -> list 'a -> int -> ML (list 'b)
let rec mapi_init f l i = match l with
    | [] -> []
    | hd::tl -> (f i hd)::(mapi_init f tl (i+1))

(*| Applies `f k x` to each element `x` of the list and its index `k`, counting
    from 0, and returns the list of results in the `ML` effect.

    This hides `FStar.List.Tot.Base.mapi`, which requires `f` to be total.
    Named as in OCaml. *)
val mapi: (int -> 'a -> ML 'b) -> list 'a -> ML (list 'b)
let mapi f l = mapi_init f l 0

(*| Applies `f` to each element of the list and concatenates the resulting
    lists, in order, in the `ML` effect.

    Equivalent to flattening `FStar.List.map f l`, and the same function as
    `FStar.List.collect`. This hides `FStar.List.Tot.Base.concatMap`, which
    requires `f` to be total. *)
val concatMap: ('a -> ML (list 'b)) -> list 'a -> ML (list 'b)
let rec concatMap f = function
  | [] -> []
  | a::tl ->
    let fa = f a in
    let ftl = concatMap f tl in
    fa @ ftl

(*| Applies `f` pointwise to two lists and returns the list of results, in the
    `ML` effect; fails with an exception if the lists have different lengths.

    Named as in OCaml. `FStar.List.Pure.Base.map2` is a pure variant that
    requires a proof that the lengths are equal. *)
val map2: ('a -> 'b -> ML 'c) -> list 'a -> list 'b -> ML (list 'c)
let rec map2 f l1 l2 = match l1, l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (f hd1 hd2)::(map2 f tl1 tl2)
    | _, _ -> failwith "The lists do not have the same length"

(*| Applies `f` pointwise to three lists and returns the list of results, in
    the `ML` effect; fails with an exception if the lists have different
    lengths.

    Named as in OCaml. `FStar.List.Pure.Base.map3` is a pure variant that
    requires a proof that the lengths are equal. *)
val map3: ('a -> 'b -> 'c -> ML 'd) -> list 'a -> list 'b -> list 'c -> ML (list 'd)
let rec map3 f l1 l2 l3 = match l1, l2, l3 with
    | [], [], [] -> []
    | hd1::tl1, hd2::tl2, hd3::tl3 -> (f hd1 hd2 hd3)::(map3 f tl1 tl2 tl3)
    | _, _, _ -> failwith "The lists do not have the same length"

(*| Combines the elements of a list from the left with an accumulator, using
    an effectful function.

    `fold_left f x [y1; y2; y3]` computes `f (f (f x y1) y2) y3`. This hides
    `FStar.List.Tot.Base.fold_left`, which requires `f` to be total. Named as
    in OCaml and Coq. *)
val fold_left: ('a -> 'b -> ML 'a) -> 'a -> list 'b -> ML 'a
let rec fold_left f x y = match y with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

(*| Combines the elements of two lists pairwise from the left with an
    accumulator, in the `ML` effect; fails with an exception if the lists have
    different lengths.

    `fold_left2 f a [x1; x2] [y1; y2]` computes `f (f a x1 y1) x2 y2`. This
    hides `FStar.List.Tot.Base.fold_left2`, which requires equal lengths to be
    proved instead. Named as in OCaml. *)
val fold_left2: ('s -> 'a -> 'b -> ML 's) -> 's -> list 'a -> list 'b -> ML 's
let rec fold_left2 f a l1 l2 = match l1, l2 with
    | [], [] -> a
    | hd1::tl1, hd2::tl2 -> fold_left2 f (f a hd1 hd2) tl1 tl2
    | _, _ -> failwith "The lists do not have the same length"

(*| Combines the elements of a list from the right with an accumulator, using
    an effectful function.

    `fold_right f [x1; x2; x3] y` computes `f x1 (f x2 (f x3 y))`; the calls to
    `f` happen from the last element to the first. This hides
    `FStar.List.Tot.Base.fold_right`, which requires `f` to be total. Named as
    in OCaml and Coq. *)
val fold_right: ('a -> 'b -> ML 'b) -> list 'a -> 'b -> ML 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

(** List searching **)

(*| Returns the elements of the list for which the effectful predicate `f`
    returns `true`, in their original order.

    This hides `FStar.List.Tot.Base.filter`, which requires `f` to be total.
    Named as in OCaml and Coq. *)
val filter: ('a -> ML bool) -> list 'a -> ML (list 'a)
let rec filter f = function
  | [] -> []
  | hd::tl -> if f hd then hd::(filter f tl) else filter f tl

(*| Returns `true` exactly when the effectful predicate `f` returns `true` on
    every element of the list; stops at the first element where it returns
    `false`.

    This hides `FStar.List.Tot.Base.for_all`, which requires `f` to be total.
    Named as in OCaml; similar to `forallb` in Coq. *)
val for_all: ('a -> ML bool) -> list 'a -> ML bool
let rec for_all f l = match l with
    | [] -> true
    | hd::tl -> if f hd then for_all f tl else false

(*| Returns `true` exactly when `f x y` returns `true` for each pair of
    elements at the same position in two lists, in the `ML` effect.

    Stops at the first pair where `f` returns `false`. Fails with an exception
    if the lists have different lengths and no earlier pair failed. Similar to
    `List.for_all2` in OCaml. *)
val forall2: ('a -> 'b -> ML bool) -> list 'a -> list 'b -> ML bool
let rec forall2 f l1 l2 = match l1,l2 with
    | [], [] -> true
    | hd1::tl1, hd2::tl2 -> if f hd1 hd2 then forall2 f tl1 tl2 else false
    | _, _ -> failwith "The lists do not have the same length"

(*| Applies `f` to each element of the list and concatenates the resulting
    lists, in order, in the `ML` effect.

    The same function as `FStar.List.concatMap`. This hides
    `FStar.List.Tot.Base.collect`, which requires `f` to be total. *)
val collect: ('a -> ML (list 'b)) -> list 'a -> ML (list 'b)
let rec collect f l = match l with
    | [] -> []
    | hd::tl -> append (f hd) (collect f tl)

(*| Returns `Some` of the first element for which the effectful predicate `p`
    returns `true`, or `None` if there is none.

    This hides `FStar.List.Tot.Base.tryFind`, which requires `p` to be total. *)
val tryFind: ('a -> ML bool) -> list 'a -> ML (option 'a)
let rec tryFind p l = match l with
    | [] -> None
    | hd::tl -> if p hd then Some hd else tryFind p tl

(*| Returns the first `Some` result of the effectful function `f` over the
    elements of the list, in order, or `None` if `f` returns `None` on all of
    them.

    This hides `FStar.List.Tot.Base.tryPick`, which requires `f` to be total. *)
val tryPick: ('a -> ML (option 'b)) -> list 'a -> ML (option 'b)
let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl

(*| Returns the list of all `y` such that `f x` returns `Some y` for an element
    `x` of the list, in order, in the `ML` effect.

    This hides `FStar.List.Tot.Base.choose`, which requires `f` to be total.
    `FStar.List.filter_map` computes the same list tail-recursively. *)
val choose: ('a -> ML (option 'b)) -> list 'a -> ML (list 'b)
let rec choose f l = match l with
    | [] -> []
    | hd::tl ->
       match f hd with
         | Some x -> x::(choose f tl)
         | None -> choose f tl

(*| Splits a list into the elements for which the effectful predicate `f`
    returns `true` and those for which it returns `false`, each in their
    original order.

    This hides `FStar.List.Tot.Base.partition`, which requires `f` to be total. *)
val partition: ('a -> ML bool) -> list 'a -> ML (list 'a & list 'a)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partition f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2

(** List of tuples **)

(*| Pairs up the elements at the same positions of two lists, in the `ML`
    effect; fails with an exception if the lists have different lengths.

    Named as in Haskell. `FStar.List.Pure.Base.zip` is a pure variant that
    requires a proof that the lengths are equal. *)
val zip: list 'a -> list 'b -> ML (list ('a & 'b))
let rec zip l1 l2 = match l1,l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (hd1,hd2)::(zip tl1 tl2)
    | _, _ -> failwith "The lists do not have the same length"

(** Sorting (implemented as quicksort) **)

(*| Sorts a list according to an effectful comparison function, using
    quicksort, in the `ML` effect.

    Unlike `FStar.List.Tot.Base.sortWith`, which it hides, this version puts
    `x` before `y` when `compare x y > 0`, so with the usual comparison
    convention it sorts in descending order. No lemma about this version is
    provided. *)
val sortWith: ('a -> 'a -> ML int) -> list 'a -> ML (list 'a)
let rec sortWith f = function
  | [] -> []
  | pivot::tl ->
     let hi, lo  = partition (fun x -> f pivot x > 0) tl in
     sortWith f lo@(pivot::sortWith f hi)

(*| Splits a list into its first `n` elements and the rest, in the `ML` effect;
    fails with an exception if the list has fewer than `n` elements.

    This hides `FStar.List.Tot.Base.splitAt`, which instead returns the whole
    list as the first part when it is too short. *)
val splitAt: nat -> list 'a -> ML (list 'a & list 'a)
let rec splitAt n l =
  if n = 0 then [], l
  else
    match l with
      | []     -> failwith "splitAt index is more that list length"
      | hd::tl ->
        let l1, l2 = splitAt (n - 1) tl in
        hd::l1, l2

(*| Returns the list of all `y` such that `f x` returns `Some y` for an element
    `x` of the list, in order, in the `ML` effect.

    The same result as `FStar.List.choose`, computed with a tail-recursive loop
    and an accumulator that is reversed at the end. *)
let filter_map (f:'a -> ML (option 'b)) (l:list 'a) : ML (list 'b) =
  let rec filter_map_acc (acc:list 'b) (l:list 'a) : ML (list 'b) =
    match l with
    | [] ->
        rev acc
    | hd :: tl ->
        match f hd with
        | Some hd ->
            filter_map_acc (hd :: acc) tl
        | None ->
            filter_map_acc acc tl
  in
  filter_map_acc [] l

(* TODO: rename this function (it hides List.Tot.index which has a
   completely different semantics.) *)

(*| Returns the position, counting from 0, of the first element for which the
    effectful predicate `f` returns `true`; fails with an exception if there is
    none.

    Unrelated to `FStar.List.Tot.Base.index`, which it hides: that function
    returns the element at a given position. `FStar.List.Tot.Properties.index_of`
    is the ghost function that finds the position of a given element. *)
val index: ('a -> ML bool) -> list 'a -> ML int
let index f l =
  let rec index l i : ML int =
    match l with
    | [] ->
        failwith "List.index: not found"
    | hd :: tl ->
        if f hd then
          i
        else
          index tl (i + 1)
  in
  index l 0
