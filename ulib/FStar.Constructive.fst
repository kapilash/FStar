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
module FStar.Constructive
(*| Constructive conjunction: a value of `cand p1 p2` is a pair of proofs.

    Its constructor `Conj` has fields `h1 : p1` and `h2 : p2`. Unlike `p1 /\ p2`,
    the proofs are computationally relevant. *)
type cand p1 p2 =
  | Conj : h1:p1 -> h2:p2 -> cand p1 p2

(*| Constructive disjunction: a value of `cor p1 p2` is a proof of one side,
    tagged with which side it is.

    Constructors: `IntroL` (field `h : p1`) and `IntroR` (field `h : p2`). *)
type cor p1 p2 =
  | IntroL : h:p1 -> cor p1 p2
  | IntroR : h:p2 -> cor p1 p2

(*| Constructive implication: a total function from proofs of `a` to proofs of
    `b`. *)
type cimp a b = a -> Tot b

(*| Constructive equivalence: a pair of `FStar.Constructive.cimp` in both
    directions. *)
type ciff a b = cand (cimp a b) (cimp b a)

(*| Constructive existential quantification: a witness `x` together with a
    proof of `p x`.

    Its constructor `ExIntro` has fields `x : a` and `h : p x`. *)
noeq type cexists (#a:Type) (p:a -> Type) = 
  | ExIntro : x:a -> h:p x -> cexists p

// val ex_intro_x : #a:Type -> #p:(a -> Type) -> projectee:cexists p -> Tot a
// let ex_intro_x #a #p = function
//   | ExIntro x _ -> x

(*| Constructive equality, as an inductive type with a single constructor
    `Refl : ceq x x`.

    Eliminated by `FStar.Constructive.eq_ind`; see also
    `FStar.Constructive.ceq_eq` to obtain a boolean equality. *)
type ceq (#a:Type) x : a -> Type =
  | Refl : ceq #a x x

(*| Constructive equality of types, with a single constructor
    `ReflType : ceq_type a a`. *)
type ceq_type (a:Type) : Type -> Type =
  | ReflType : ceq_type a a

(*| The induction principle of `FStar.Constructive.ceq`: from `p x` and
    `ceq x y`, gives `p y`. *)
val eq_ind : #a:Type -> x:a -> p:(a -> Type) -> f:p x -> y:a -> e:ceq x y -> Tot (p y)
let eq_ind #a x p f y _ = f

(*| A constructive equality `ceq x y` on a type with decidable equality
    implies `x = y`. *)
val ceq_eq : #a:Type{hasEq a} -> #x:a -> #y:a -> h:(ceq x y) -> Lemma (x = y)
let ceq_eq #a #x #y h = ()

(*| Constructive equality is a congruence: `ceq x y` implies
    `ceq (f x) (f y)` for any (ghost) function `f`. *)
val ceq_congruence : #a:Type -> #b:Type -> #x:a -> #y:a -> ceq x y ->
                     f:(a -> GTot b) -> GTot (ceq (f x) (f y))
let ceq_congruence #a #b #x #y h f = Refl #_ #(f x) //refuse to infer terms with non-Tot effect

(*| Constructive equality is symmetric: `ceq x y` implies `ceq y x`. *)
val ceq_symm : #a:Type -> #x:a -> #y:a -> ceq x y -> Tot (ceq y x)
let ceq_symm #a #x #y h = Refl

(*| Constructive equality is transitive: `ceq x y` and `ceq y z` imply
    `ceq x z`. *)
val ceq_trans : #a:Type -> #x:a -> #y:a -> #z:a -> ceq x y -> ceq y z -> Tot (ceq x z)
let ceq_trans #a #x #y #z hxy hyz = Refl

(*| Constructive truth: a type with the single inhabitant `I`. *)
type ctrue =
  | I : ctrue

(* hopefully this is an empty type *)
(*| Constructive falsehood: an inductive type with no constructors.

    Eliminated by `FStar.Constructive.cfalse_elim`. *)
type cfalse : Type =

(*| Ex falso for constructive falsehood: from a value of
    `FStar.Constructive.cfalse`, produces a value of any type, by an empty
    pattern match. *)
val cfalse_elim : #a:Type -> cfalse -> Tot a
let cfalse_elim #a f = match f with

(*| Ex falso for constructive falsehood, like `FStar.Constructive.cfalse_elim`
    but proved through `FStar.Pervasives.false_elim` instead of a pattern
    match. *)
val false_elim2 : #a:Type -> cfalse -> Tot a
let false_elim2 #a x = false_elim ()

(*| Produces a value of any type in a context where `false` holds, i.e. in
    unreachable code.

    Shadows `FStar.Pervasives.false_elim`, which it calls. *)
val false_elim : #a:Type -> u:unit{false} -> Tot a
let false_elim #a u = false_elim ()

(*| Constructive negation: `cnot p` is `FStar.Constructive.cimp p cfalse`. *)
type cnot (p:Type) = cimp p cfalse
