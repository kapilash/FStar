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
module FStar.Algebra.Monoid

open FStar.Classical
module PropExt = FStar.PropositionalExtensionality

(*
 * AR: 05/12: adding calls to equational lemmas from PropositionalExtensionality
 *            these should go away with proper prop support
 *            also see the comment in PropositionalExtensionality.fst
 *)

(** Definition of a monoid *)

(*| States that `u` is a right identity for `mult`: `mult x u == x` for all `x`.

    A quantified `prop` with SMT pattern `mult x u`; used as a field of
    `FStar.Algebra.Monoid.monoid`. *)
let right_unitality_lemma (m:Type) (u:m) (mult:m -> m -> m) =
  forall (x:m). {:pattern (x `mult` u)} x `mult` u == x

(*| States that `u` is a left identity for `mult`: `mult u x == x` for all `x`.

    A quantified `prop` with SMT pattern `mult u x`; used as a field of
    `FStar.Algebra.Monoid.monoid`. *)
let left_unitality_lemma (m:Type) (u:m) (mult:m -> m -> m) =
  forall (x:m). {:pattern (u `mult` x)} u `mult` x == x

(*| States that `mult` is associative: `mult (mult x y) z == mult x (mult y z)`
    for all `x`, `y` and `z`.

    A quantified `prop` with SMT pattern `mult (mult x y) z`; used as a field of
    `FStar.Algebra.Monoid.monoid`. *)
let associativity_lemma (m:Type) (mult:m -> m -> m) =
  forall (x y z:m). {:pattern (x `mult` y `mult` z)} x `mult` y `mult` z == x `mult` (y `mult` z)

(*| A monoid on `m`, with laws up to propositional equality `==`.

    The single constructor `Monoid` has the fields:

    - `unit`: the neutral element.
    - `mult`: the binary operation.
    - `right_unitality`: a proof of `FStar.Algebra.Monoid.right_unitality_lemma`.
    - `left_unitality`: a proof of `FStar.Algebra.Monoid.left_unitality_lemma`.
    - `associativity`: a proof of `FStar.Algebra.Monoid.associativity_lemma`.

    The laws are squashed propositions; build a monoid with
    `FStar.Algebra.Monoid.intro_monoid`. For commutative monoids, see
    `FStar.Algebra.CommMonoid.cm` and `FStar.Algebra.CommMonoid.Equiv.cm`. *)
unopteq
type monoid (m:Type) =
  | Monoid :
    unit:m ->
    mult:(m -> m -> m) ->
    right_unitality:squash (right_unitality_lemma m unit mult) ->
    left_unitality:squash (left_unitality_lemma m unit mult) ->
    associativity:squash (associativity_lemma m mult) ->
    monoid m


(*| Builds a `FStar.Algebra.Monoid.monoid` from a unit and an operation, given
    that the three monoid laws hold.

    The result has exactly the given `unit` and `mult`. *)
let intro_monoid (m:Type) (u:m) (mult:m -> m -> m)
  : Pure (monoid m)
    (requires (right_unitality_lemma m u mult /\ left_unitality_lemma m u mult /\ associativity_lemma m mult))
    (ensures (fun mm -> Monoid?.unit mm == u /\ Monoid?.mult mm == mult))
=
  Monoid u mult () () ()


(** Some monoid structures *)

(*| The monoid of natural numbers under addition, with unit `0`. *)
let nat_plus_monoid : monoid nat =
  let add (x y : nat) : nat = x + y in
  intro_monoid nat 0 add

(*| The monoid of integers under addition, with unit `0`. *)
let int_plus_monoid : monoid int =
  intro_monoid int 0 (+)

(* let int_mul_monoid : monoid int = *)
(*   intro_monoid int 1 op_Star *)

(*| The monoid of propositions under conjunction `p /\ q`, with unit `True`.

    The laws hold with `==` thanks to propositional extensionality
    (`FStar.PropositionalExtensionality`). *)
let conjunction_monoid : monoid prop =
  let u : prop = singleton True in
  let mult (p q : prop) : prop = p /\ q in

  let left_unitality_helper (p:prop) : Lemma ((u `mult` p) == p) =
    assert ((u `mult` p) <==> p) ;
    PropExt.apply (u `mult` p) p
  in

  let right_unitality_helper (p:prop) : Lemma ((p `mult` u) == p) =
    assert ((p `mult` u) <==> p) ;
    PropExt.apply (p `mult` u) p
  in

  let associativity_helper (p1 p2 p3 : prop) : Lemma (p1 `mult` p2 `mult` p3 == p1 `mult` (p2 `mult` p3)) =
    assert (p1 `mult` p2 `mult` p3 <==> p1 `mult` (p2 `mult` p3)) ;
    PropExt.apply (p1 `mult` p2 `mult` p3) (p1 `mult` (p2 `mult` p3))
  in

  forall_intro right_unitality_helper ;
  assert (right_unitality_lemma prop u mult) ;
  forall_intro left_unitality_helper ;
  assert (left_unitality_lemma prop u mult) ;
  forall_intro_3 associativity_helper;
  assert (associativity_lemma prop mult) ;
  intro_monoid prop u mult


(*| The monoid of propositions under disjunction `p \/ q`, with unit `False`.

    The laws hold with `==` thanks to propositional extensionality
    (`FStar.PropositionalExtensionality`). *)
let disjunction_monoid : monoid prop =
  let u : prop = singleton False in
  let mult (p q : prop) : prop = p \/ q in

  let left_unitality_helper (p:prop) : Lemma ((u `mult` p) == p) =
    assert ((u `mult` p) <==> p) ;
    PropExt.apply (u `mult` p) p
  in

  let right_unitality_helper (p:prop) : Lemma ((p `mult` u) == p) =
    assert ((p `mult` u) <==> p) ;
    PropExt.apply (p `mult` u) p
  in

  let associativity_helper (p1 p2 p3 : prop) : Lemma (p1 `mult` p2 `mult` p3 == p1 `mult` (p2 `mult` p3)) =
    assert (p1 `mult` p2 `mult` p3 <==> p1 `mult` (p2 `mult` p3)) ;
    PropExt.apply (p1 `mult` p2 `mult` p3) (p1 `mult` (p2 `mult` p3))
  in

  forall_intro right_unitality_helper ;
  assert (right_unitality_lemma prop u mult) ;
  forall_intro left_unitality_helper ;
  assert (left_unitality_lemma prop u mult) ;
  forall_intro_3 associativity_helper;
  assert (associativity_lemma prop mult) ;
  intro_monoid prop u mult

(*| The monoid of booleans under `&&`, with unit `true`. *)
let bool_and_monoid : monoid bool =
  let and_ b1 b2 = b1 && b2 in
  intro_monoid bool true and_

(*| The monoid of booleans under `||`, with unit `false`. *)
let bool_or_monoid : monoid bool =
  let or_ b1 b2 = b1 || b2 in
  intro_monoid bool false or_

(*| The monoid of booleans under exclusive or, with unit `false`. *)
let bool_xor_monoid : monoid bool =
  let xor b1 b2 = (b1 || b2) && not (b1 && b2) in
  intro_monoid bool false xor

(*| Lifts a monoid on `a` to `option a`, with unit `Some m.unit`.

    Two `Some` values multiply as in `m`; any product involving `None` is
    `None`, so `None` is absorbing. *)
let lift_monoid_option (#a:Type) (m:monoid a) : monoid (option a) =
  let mult (x y:option a) =
    match x, y with
    | Some x0, Some y0 -> Some (m.mult x0 y0)
    | _, _ -> None
  in
  intro_monoid (option a) (Some m.unit) mult

(* Definition of a morphism of monoid *)

(*| States that `f` maps the unit of `ma` to the unit of `mb`. *)
let monoid_morphism_unit_lemma (#a #b:Type) (f:a -> b) (ma:monoid a) (mb:monoid b) =
  f (Monoid?.unit ma) == Monoid?.unit mb

(*| States that `f` commutes with multiplication: `mb.mult (f x) (f y) == f (ma.mult x y)`
    for all `x` and `y`. *)
let monoid_morphism_mult_lemma (#a #b:Type) (f:a -> b) (ma:monoid a) (mb:monoid b) =
  forall (x y:a). Monoid?.mult mb (f x) (f y) == f (Monoid?.mult ma x y)

(*| A proof that `f` is a monoid morphism from `ma` to `mb`.

    The single constructor `MonoidMorphism` has the squashed fields `unit`
    (`FStar.Algebra.Monoid.monoid_morphism_unit_lemma`) and `mult`
    (`FStar.Algebra.Monoid.monoid_morphism_mult_lemma`). Build one with
    `FStar.Algebra.Monoid.intro_monoid_morphism`. *)
type monoid_morphism (#a #b:Type) (f:a -> b) (ma:monoid a) (mb:monoid b) =
  | MonoidMorphism :
    unit:squash (monoid_morphism_unit_lemma f ma mb) ->
    mult:squash (monoid_morphism_mult_lemma f ma mb) ->
    monoid_morphism f ma mb

(*| Builds a `FStar.Algebra.Monoid.monoid_morphism` for `f` from proofs that it
    preserves the unit and multiplication. *)
let intro_monoid_morphism (#a #b:Type) (f:a -> b) (ma:monoid a) (mb:monoid b)
  : Pure (monoid_morphism f ma mb)
    (requires (monoid_morphism_unit_lemma f ma mb /\ monoid_morphism_mult_lemma f ma mb))
    (ensures (fun _ -> True))
=
  MonoidMorphism () ()

(*| The inclusion of `nat` into `int`.

    It is a monoid morphism from `FStar.Algebra.Monoid.nat_plus_monoid` to
    `FStar.Algebra.Monoid.int_plus_monoid`; the module checks this. *)
let embed_nat_int (n:nat) : int = n
let _ = intro_monoid_morphism embed_nat_int nat_plus_monoid int_plus_monoid

(*| Propositional negation `~p`, as a function on `prop`.

    The module checks that it is a monoid morphism from
    `FStar.Algebra.Monoid.conjunction_monoid` to
    `FStar.Algebra.Monoid.disjunction_monoid` and back (De Morgan's laws). *)
let neg (p:prop) : prop = ~p
let _ =
  assert (neg True <==> False) ;
  PropExt.apply (neg True) False ;
  let mult_lemma_helper (p q:prop) : Lemma (neg (p /\ q) == (neg p \/ neg q)) =
    assert (neg (p /\ q) <==> (neg p \/ neg q)) ;
    PropExt.apply (neg (p /\ q)) (neg p \/ neg q)
  in
  forall_intro_2 mult_lemma_helper ;
  intro_monoid_morphism neg conjunction_monoid disjunction_monoid

let _ =
  assert (neg False <==> True) ;
  PropExt.apply (neg False) True ;
  let mult_lemma_helper (p q:prop) : Lemma (neg (p \/ q) == (neg p /\ neg q)) =
    assert (neg (p \/ q) <==> (neg p /\ neg q)) ;
    PropExt.apply (neg (p \/ q)) (neg p /\ neg q)
  in
  forall_intro_2 mult_lemma_helper ;
  intro_monoid_morphism neg disjunction_monoid conjunction_monoid

(* Definition of a left action *)

(*| States the compatibility of an action with multiplication:
    `act (mult x x') y == act x (act x' y)` for all `x`, `x'` and `y`. *)
let mult_act_lemma (m a:Type) (mult:m -> m -> m) (act:m -> a -> a) =
  forall (x x':m) (y:a). (x `mult` x') `act` y == x `act` (x' `act` y)

(*| States that the unit acts trivially: `act u y == y` for all `y`. *)
let unit_act_lemma (m a:Type) (u:m) (act:m -> a -> a) =
  forall (y:a). u `act` y == y

(*| A left action of the monoid `mm` on the type `a`.

    The single constructor `LAct` has the fields `act`, the action, and the
    squashed laws `mult_lemma` (`FStar.Algebra.Monoid.mult_act_lemma`) and
    `unit_lemma` (`FStar.Algebra.Monoid.unit_act_lemma`). *)
unopteq
type left_action (#m:Type) (mm:monoid m) (a:Type) =
  | LAct :
    act:(m -> a -> a) ->
    mult_lemma: squash (mult_act_lemma m a (Monoid?.mult mm) act) ->
    unit_lemma: squash (unit_act_lemma m a (Monoid?.unit mm) act) ->
    left_action mm a

(*| States that `f` is equivariant between the left actions `la` and `lb`, along
    `mf`: `lb.act (mf g) (f x) == f (la.act g x)` for all `g` and `x`.

    `mf` is meant to be a monoid morphism, but the property does not require it. *)
let left_action_morphism
    (#a #b #ma #mb:Type)
    (f:a -> b)
    (* mf ought to be a monoid morphism but we don't use this fact in the property *)
    (mf: ma -> mb)
    (#mma:monoid ma)
    (#mmb:monoid mb)
    (la:left_action mma a)
    (lb:left_action mmb b)
= forall (g:ma) (x:a). LAct?.act lb (mf g) (f x) == f (LAct?.act la g x)
