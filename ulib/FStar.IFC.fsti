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

module FStar.IFC

/// FStar.IFC provides a simple, generic abstraction for monadic
/// information-flow control based on a user-defined (semi-)lattice of
/// information flow labels.
///
/// The main idea is to provide an abstract type [protected a l],
/// encapsulating values of type [a] carrying information at
/// confidentiality level [l]. Operations that compute on the
/// underlying [a] are instrumented to reflect the sensitivity of
/// their arguments on their results.
///
/// Several papers develop this idea, ranging from
///
/// Fable: A language for enforcing user-defined security policies
/// http://www.cs.umd.edu/~nswamy/papers/fable-tr.pdf
///
/// To more modern variants like
/// https://hackage.haskell.org/package/lio

(**** Basic definitions for a join semilattice *)

(*| States that the binary operation `f` is associative: `f (f x y) z == f x (f y z)` for all `x`, `y` and `z`. *)
let associative #a (f: (a -> a -> a)) = forall x y z. f (f x y) z == f x (f y z)

(*| States that the binary operation `f` is commutative: `f x y == f y x` for all `x` and `y`. *)
let commutative #a (f: (a -> a -> a)) = forall x y. f x y == f y x

(*| States that the binary operation `f` is idempotent: `f x x == x` for all `x`. *)
let idempotent #a (f: (a -> a -> a)) = forall x. f x x == x

(*| A join semilattice of information-flow labels, given as a record of operations rather than a typeclass.

    The single constructor `SemiLattice` has the fields:

    - `carrier`: the type of labels (implicit).
    - `top`: a distinguished top label.
    - `lub`: the least upper bound, which must be associative, commutative and idempotent.

    The `top` field is not required to be an upper bound of every label.
    Equality is not decidable (`noeq`).

    ```fstar
    let bool_sl : FStar.IFC.sl u#0 =
      FStar.Ghost.hide (FStar.IFC.SemiLattice #bool true (fun x y -> x || y))
    ``` *)
noeq
type semilattice : Type u#(c + 1) =
  | SemiLattice : 
      #carrier: Type u#c ->
      top: carrier ->
      lub: (f: (carrier -> carrier -> carrier){associative f /\ commutative f /\ idempotent f})
    -> semilattice

(*| An erased `FStar.IFC.semilattice`, which is how semilattices are passed in the rest of the module. *)
let sl:Type u#(c + 1) = FStar.Ghost.erased semilattice

(*| The labels of a semilattice: erased elements of its carrier type. *)
let lattice_element (sl: sl) = Ghost.erased (SemiLattice?.carrier (Ghost.reveal sl))

(*| Joins two labels with the semilattice's least upper bound operator. *)
unfold
let lub #sl (x: lattice_element sl) (y: lattice_element sl) : Tot (lattice_element sl) =
  Ghost.hide (SemiLattice?.lub (Ghost.reveal sl) (Ghost.reveal x) (Ghost.reveal y))

(*| The abstract type of values of type `b` protected at information-flow label `l`.

    `protected l b` is in bijection with `b`, as witnessed by `FStar.IFC.hide`
    and `FStar.IFC.reveal`. Anything can be protected, so the type only enforces
    confidentiality: code can compute on a protected value only through
    `FStar.IFC.map`, `FStar.IFC.join` and `let>>`, whose results are protected
    at least as highly as their inputs.

    ```fstar
    let bool_sl : FStar.IFC.sl u#0 =
      FStar.Ghost.hide (FStar.IFC.SemiLattice #bool true (fun x y -> x || y))

    let secret : FStar.IFC.lattice_element bool_sl = FStar.Ghost.hide true

    let incr (x: FStar.IFC.protected secret int) : FStar.IFC.protected secret int =
      FStar.IFC.map x (fun y -> y + 1)
    ``` *)
val protected (#sl: sl u#c) (l: lattice_element sl) (b: Type u#b) : Type u#b

(*| Projects the underlying value out of a protected value; it is `GTot`, so the value is available only in specifications. *)
val reveal (#sl: _) (#l: lattice_element sl) (#b: _) (x: protected l b) : GTot b

(*| Protects a value at any label.

    Any value may be promoted to `protected l b`: protection controls only
    confidentiality, not integrity. *)
val hide (#sl: _) (#l: lattice_element sl) (#b: _) (x: b) : Tot (protected l b)

(*| Proves `reveal (hide x) == x`. Triggered automatically on `hide x`. *)
val reveal_hide (#l #t #b: _) (x: b) : Lemma (reveal (hide #l #t x) == x) [SMTPat (hide #l #t x)]

(*| Proves `hide (reveal x) == x`. Triggered automatically on `reveal x`. *)
val hide_reveal (#sl: _) (#l: lattice_element sl) (#b: _) (x: protected l b)
    : Lemma (hide (reveal x) == x) [SMTPat (reveal x)]

/// [protected l b] is a form of parameterized monad
///  It provides:
///    -- [return] (via [hide])
///    -- [map]    (i.e., it's a functor)
///    -- [join]   (so it's also a monad)
///  Which we package up as a [bind]

(*| Protects a value at the given label; the monadic return, defined as `FStar.IFC.hide`. *)
unfold
let return #sl #a (l: lattice_element sl) (x: a) : protected l a = hide x

(*| Applies a function to a protected value, keeping its label: `reveal (map x f) == f (reveal x)`.

    The arguments are in the order `map x f` rather than `map f x`, so that the
    type of `f` can depend on `x`: `f` receives the argument refined to be equal
    to `reveal x`. *)
val map (#a #b #sl: _) (#l: lattice_element sl) (x: protected l a) (f: (y: a{y == reveal x} -> b))
    : Tot (y: protected l b {reveal y == f (reveal x)})

(*| Flattens a doubly protected value; the result label is the `lub` of the two labels, and `reveal (join x) == reveal (reveal x)`.

    This is the monadic join, except that the labels are combined. *)
val join (#sl: _) (#l1 #l2: lattice_element sl) (#a: _) (x: protected l1 (protected l2 a))
    : Tot (y: protected (l1 `lub` l2) a {reveal y == reveal (reveal x)})

(*| Binds a protected value: `let>> y = x in f y` is `join (map x f)`, and its label is the `lub` of the labels of `x` and the result of `f`.

    As in `FStar.IFC.map`, the continuation receives the value refined to be
    equal to `reveal x`. Any computation that observes the value of `x` is
    therefore protected at least as highly as `x` itself. *)
unfold
let (let>>)
      #sl
      (#l1: lattice_element sl)
      #a
      (x: protected l1 a)
      (#l2: lattice_element sl)
      #b
      (f: (y: a{y == reveal x} -> protected l2 b))
    : Tot (protected (l1 `lub` l2) b) = join (map x f)

