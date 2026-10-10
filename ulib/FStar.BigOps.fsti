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

module FStar.BigOps

/// This library provides propositional connectives over finite sets
/// expressed as lists, aka "big operators", in analogy with LaTeX
/// usage for \bigand, \bigor, etc.
///
/// The library is designed with a dual usage in mind:
///
///     1. Normalization: When applied to a list literal, we want
///        {[big_and f [a;b;c]]} to implicilty reduce to [f a /\ f b /\ f c]
///
///     2. Symbolic manipulation: We provide lemmas of the form
///
///        [big_and f l <==> forall x. L.memP x l ==> f x]
///
/// In this latter form, partially computing [big_and] as a fold over
/// a list is cumbersome for proof. So, we provide variants [big_and']
/// etc., that do not reduce implicitly.

module L = FStar.List.Tot.Base

(*| A marker attribute: definitions tagged `[@@__reduce__]` are unfolded by
    `FStar.BigOps.normal`.

    It is used through the `delta_attr` normalization step; see
    `FStar.Pervasives.delta_attr`. *)
let __reduce__ = ()

(*| Normalizes `x` with the steps used by the implicitly reducing operators of
    this module.

    It unfolds definitions tagged `FStar.BigOps.__reduce__`, as well as
    `FStar.List.Tot.Base.fold_right_gtot` and `FStar.List.Tot.Base.map_gtot`,
    and performs `iota`, `zeta`, `primops` and `simplify` reduction. On a list
    literal, `FStar.BigOps.big_and f [a; b; c]` thus becomes `f a /\ f b /\ f c`. *)
[@@ __reduce__]
unfold
let normal (#a: Type) (x: a) : a =
  FStar.Pervasives.norm [
      iota;
      zeta;
      delta_only [`%L.fold_right_gtot; `%L.map_gtot];
      delta_attr [`%__reduce__];
      primops;
      simplify
    ]
    x

(*| Proves that `FStar.BigOps.normal f` is equal to `f`.

    Use it to move between an implicitly reducing operator, such as
    `FStar.BigOps.big_and`, and its non-reducing variant, such as
    `FStar.BigOps.big_and'`. *)
val normal_eq (#a: Type) (f: a) : Lemma (f == normal f)

(**** Map and fold *)

(*| Maps each element of `l` with `f` and combines the results with `op`,
    starting from `z` on the right: `op (f x1) (op (f x2) (... z))`.

    A ghost fold, defined with `FStar.List.Tot.Base.fold_right_gtot`. Its
    equations are `FStar.BigOps.map_op'_nil` and `FStar.BigOps.map_op'_cons`. *)
[@@ __reduce__]
let map_op' #a #b #c (op: (b -> c -> GTot c)) (f: (a -> GTot b)) (l: list a) (z: c) : GTot c =
  L.fold_right_gtot #a #c l (fun x acc -> (f x) `op` acc) z

(*| Proves that `FStar.BigOps.map_op'` on the empty list is the initial value `z`. *)
val map_op'_nil (#a #b #c: Type) (op: (b -> c -> GTot c)) (f: (a -> GTot b)) (z: c)
    : Lemma (map_op' op f [] z == z)

(*| Proves that `FStar.BigOps.map_op'` on `hd :: tl` is `op (f hd) (map_op' op f tl z)`. *)
val map_op'_cons
      (#a #b #c: Type)
      (op: (b -> c -> GTot c))
      (f: (a -> GTot b))
      (hd: a)
      (tl: list a)
      (z: c)
    : Lemma (map_op' op f (hd :: tl) z == (f hd) `op` (map_op' op f tl z))

(**** Conjunction *)

(*| The conjunction of `f x` for all elements `x` of the list `l`; `True` on the
    empty list.

    This variant does not reduce implicitly, which suits symbolic reasoning
    with `FStar.BigOps.big_and'_nil`, `FStar.BigOps.big_and'_cons` and
    `FStar.BigOps.big_and'_forall`:

    ```fstar
    let all_positive' (l: list nat)
      : Lemma (requires FStar.BigOps.big_and' (fun (x: nat) -> x > 0) l)
              (ensures forall x. FStar.List.Tot.memP x l ==> x > 0)
      = FStar.BigOps.big_and'_forall (fun (x: nat) -> x > 0) l
    ```

    `FStar.BigOps.big_and` is the implicitly reducing variant. *)
[@@ __reduce__]
let big_and' #a (f: (a -> prop)) (l: list a) : prop = map_op' l_and f l True

(*| Proves that `FStar.BigOps.big_and'` over the empty list is `True`. *)
val big_and'_nil (#a: Type) (f: (a -> prop)) : Lemma (big_and' f [] == True)

(*| Proves that `FStar.BigOps.big_and'` over `hd :: tl` is `f hd /\ big_and' f tl`. *)
val big_and'_cons (#a: Type) (f: (a -> prop)) (hd: a) (tl: list a)
    : Lemma (big_and' f (hd :: tl) == (f hd /\ big_and' f tl))

(*| Proves that `FStar.BigOps.big_and' f l` holds if and only if `f x` holds for
    every `x` in `l` (by `FStar.List.Tot.Base.memP`). *)
val big_and'_forall (#a: Type) (f: (a -> prop)) (l: list a)
    : Lemma (big_and' f l <==> (forall x. L.memP x l ==> f x))

(*| The conjunction of `f x` for all elements `x` of `l`, which reduces
    implicitly when `l` is a list literal.

    It is `FStar.BigOps.big_and'` wrapped in `FStar.BigOps.normal`, so
    `big_and f [a; b; c]` becomes `f a /\ f b /\ f c` during type checking:

    ```fstar
    let all_positive () : Lemma (FStar.BigOps.big_and (fun (x: int) -> x > 0) [1; 2; 3]) = ()
    ```

    For a list that is not a literal, reason about `FStar.BigOps.big_and'`
    instead, using `FStar.BigOps.normal_eq` if needed. *)
[@@ __reduce__]
unfold
let big_and #a (f: (a -> prop)) (l: list a) : prop =
  normal (big_and' f l)

(**** Disjunction *)

(*| The disjunction of `f x` for all elements `x` of the list `l`; `False` on
    the empty list.

    This variant does not reduce implicitly; its lemmas are
    `FStar.BigOps.big_or'_nil`, `FStar.BigOps.big_or'_cons` and
    `FStar.BigOps.big_or'_exists`. `FStar.BigOps.big_or` is the implicitly
    reducing variant. *)
[@@ __reduce__]
let big_or' #a (f: (a -> prop)) (l: list a) : prop = map_op' l_or f l False

(*| Proves that `FStar.BigOps.big_or'` over the empty list is `False`. *)
val big_or'_nil (#a: Type) (f: (a -> prop)) : Lemma (big_or' f [] == False)

(*| Proves that `FStar.BigOps.big_or'` over `hd :: tl` is `f hd \/ big_or' f tl`. *)
val big_or'_cons (#a: Type) (f: (a -> prop)) (hd: a) (tl: list a)
    : Lemma (big_or' f (hd :: tl) == (f hd \/ big_or' f tl))

(*| Proves that `FStar.BigOps.big_or' f l` holds if and only if `f x` holds for
    some `x` in `l` (by `FStar.List.Tot.Base.memP`). *)
val big_or'_exists (#a: Type) (f: (a -> prop)) (l: list a)
    : Lemma (big_or' f l <==> (exists x. L.memP x l /\ f x))

(*| The disjunction of `f x` for all elements `x` of `l`, which reduces
    implicitly when `l` is a list literal.

    It is `FStar.BigOps.big_or'` wrapped in `FStar.BigOps.normal`, so
    `big_or f [a; b; c]` becomes `f a \/ f b \/ f c`. *)
[@@ __reduce__]
unfold
let big_or #a (f: (a -> prop)) (l: list a) : prop =
  normal (big_or' f l)

(**** Pairwise operators *)

/// We provide functions to apply a reflexive, symmetric binary
/// operator to elements in a list [l] pairwise, in a triangle of
/// elements in the square matrix of [l X l]. To illustrate, for a
/// list of [n] elements, we fold the operator over the pairwise
/// elements of the list in top-down, left-to-right order of the
/// diagram below
///
///
///  {[
///     0 1 2 3 ... n
///   0
///   1 x
///   2 x x
///   3 x x x
///   . x x x x
///   n x x x x  ]}

(*| Combines `f x y` with `op` over all pairs of elements of `l` where `x`
    occurs before `y`, starting from `z`.

    For `l = [a; b; c]` it visits the pairs `(a, b)`, `(a, c)` and `(b, c)`:
    the strict lower triangle of `l` times `l`, without the diagonal. A ghost
    function, used to define `FStar.BigOps.pairwise_and'` and
    `FStar.BigOps.pairwise_or'`. *)
[@@ __reduce__]
let rec pairwise_op' #a #b (op: (b -> b -> GTot b)) (f: (a -> a -> b)) (l: list a) (z: b) : GTot b =
  match l with
  | [] -> z
  | hd :: tl -> (map_op' op (f hd) tl z) `op` (pairwise_op' op f tl z)

(*| States that the relation `f` is symmetric: `f x y <==> f y x` for all `x`
    and `y`. *)
let symmetric (#a: Type) (f: (a -> a -> prop)) = forall x y. f x y <==> f y x

(*| States that the relation `f` is reflexive: `f x x` for all `x`. *)
let reflexive (#a: Type) (f: (a -> a -> prop)) = forall x. f x x

(*| States that the relation `f` is irreflexive: `~(f x x)` for all `x`. *)
let anti_reflexive (#a: Type) (f: (a -> a -> prop)) = forall x. ~(f x x)

(**** Pairwise conjunction *)

(*| The conjunction of `f x y` over all pairs of elements of `l` where `x`
    occurs before `y`; `True` on lists with fewer than two elements.

    For example, `pairwise_and' f [a; b; c]` is `f a b /\ f a c /\ f b c`. A
    typical use is pairwise disjointness. This variant does not reduce
    implicitly; `FStar.BigOps.pairwise_and` does. *)
[@@ __reduce__]
let pairwise_and' #a (f: (a -> a -> prop)) (l: list a) : prop = pairwise_op' l_and f l True

(*| Proves that `FStar.BigOps.pairwise_and'` over the empty list is `True`. *)
val pairwise_and'_nil (#a: Type) (f: (a -> a -> prop)) : Lemma (pairwise_and' f [] == True)

(*| Proves that `FStar.BigOps.pairwise_and'` over `hd :: tl` is
    `big_and' (f hd) tl /\ pairwise_and' f tl`. *)
val pairwise_and'_cons (#a: Type) (f: (a -> a -> prop)) (hd: a) (tl: list a)
    : Lemma (pairwise_and' f (hd :: tl) == (big_and' (f hd) tl /\ pairwise_and' f tl))

(*| Proves that, for a symmetric and reflexive relation `f`,
    `FStar.BigOps.pairwise_and' f l` holds if and only if `f x y` holds for all
    `x` and `y` in `l`. *)
val pairwise_and'_forall (#a: Type) (f: (a -> a -> prop)) (l: list a)
    : Lemma (requires symmetric f /\ reflexive f)
      (ensures (pairwise_and' f l <==> (forall x y. L.memP x l /\ L.memP y l ==> f x y)))

(*| Proves that, for a symmetric relation `f` and a list `l` without repeated
    elements, `FStar.BigOps.pairwise_and' f l` holds if and only if `f x y`
    holds for all distinct `x` and `y` in `l`.

    The precondition on `l` is `FStar.List.Tot.Base.no_repeats_p`. *)
val pairwise_and'_forall_no_repeats (#a: Type) (f: (a -> a -> prop)) (l: list a)
    : Lemma (requires symmetric f /\ L.no_repeats_p l)
      (ensures (pairwise_and' f l <==> (forall x y. L.memP x l /\ L.memP y l /\ x =!= y ==> f x y)))

(*| The conjunction of `f x y` over all pairs of elements of `l` where `x`
    occurs before `y`, which reduces implicitly when `l` is a list literal.

    It is `FStar.BigOps.pairwise_and'` wrapped in `FStar.BigOps.normal`. *)
[@@ __reduce__]
unfold
let pairwise_and #a (f: (a -> a -> prop)) (l: list a) : prop =
  normal (pairwise_and' f l)

(**** Pairwise disjunction *)

(*| The disjunction of `f x y` over all pairs of elements of `l` where `x`
    occurs before `y`; `False` on lists with fewer than two elements.

    For example, `pairwise_or' f [a; b; c]` is `f a b \/ f a c \/ f b c`. This
    variant does not reduce implicitly; `FStar.BigOps.pairwise_or` does. *)
[@@ __reduce__]
let pairwise_or' #a (f: (a -> a -> prop)) (l: list a) : prop = pairwise_op' l_or f l False

(*| Proves that `FStar.BigOps.pairwise_or'` over the empty list is `False`. *)
val pairwise_or'_nil (#a: Type) (f: (a -> a -> prop)) : Lemma (pairwise_or' f [] == False)

(*| Proves that `FStar.BigOps.pairwise_or'` over `hd :: tl` is
    `big_or' (f hd) tl \/ pairwise_or' f tl`. *)
val pairwise_or'_cons (#a: Type) (f: (a -> a -> prop)) (hd: a) (tl: list a)
    : Lemma (pairwise_or' f (hd :: tl) == (big_or' (f hd) tl \/ pairwise_or' f tl))

(*| Proves that, for a symmetric and irreflexive relation `f`,
    `FStar.BigOps.pairwise_or' f l` holds if and only if `f x y` holds for some
    `x` and `y` in `l`. *)
val pairwise_or'_exists (#a: Type) (f: (a -> a -> prop)) (l: list a)
    : Lemma (requires symmetric f /\ anti_reflexive f)
      (ensures (pairwise_or' f l <==> (exists x y. L.memP x l /\ L.memP y l /\ f x y)))

(*| Proves that, for a symmetric relation `f` and a list `l` without repeated
    elements, `FStar.BigOps.pairwise_or' f l` holds if and only if `f x y`
    holds for some distinct `x` and `y` in `l`.

    The precondition on `l` is `FStar.List.Tot.Base.no_repeats_p`. *)
val pairwise_or'_exists_no_repeats (#a: Type) (f: (a -> a -> prop)) (l: list a)
    : Lemma (requires symmetric f /\ L.no_repeats_p l)
      (ensures (pairwise_or' f l <==> (exists x y. L.memP x l /\ L.memP y l /\ x =!= y /\ f x y)))

(*| The disjunction of `f x y` over all pairs of elements of `l` where `x`
    occurs before `y`, which reduces implicitly when `l` is a list literal.

    It is `FStar.BigOps.pairwise_or'` wrapped in `FStar.BigOps.normal`. *)
[@@ __reduce__]
unfold
let pairwise_or #a (f: (a -> a -> prop)) (l: list a) : prop =
  normal (pairwise_or' f l)

