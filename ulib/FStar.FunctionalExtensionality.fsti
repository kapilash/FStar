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

module FStar.FunctionalExtensionality

/// Functional extensionality asserts the equality of pointwise-equal
/// functions.
///
/// The formulation of this axiom is particularly subtle in F* because
/// of its interaction with subtyping. In fact, prior formulations of
/// this axiom were discovered to be unsound by Aseem Rastogi.
///
/// The predicate [feq #a #b f g] asserts that [f, g: x:a -> (b x)] are
/// pointwise equal on the domain [a].
///
/// However, due to subtyping [f] and [g] may also be defined on some
/// domain larger than [a]. We need to be careful to ensure that merely
/// proving [f] and [g] equal on their sub-domain [a] does not lead us
/// to conclude that they are equal everywhere.
///
/// For more context on how functional extensionality works in F*, see
///   1. tests/micro-benchmarks/Test.FunctionalExtensionality.fst
///   2. ulib/FStar.Map.fst and ulib/FStar.Map.fsti
///   3. Issue #1542 on github.com/FStarLang/FStar/issues/1542

(*| The type of total, dependent functions from `a` to `b`. *)
unfold
let arrow (a: Type) (b: (a -> Type)) = x: a -> Tot (b x)

(*| Deprecated alias of `FStar.FunctionalExtensionality.arrow`. *)
[@@ (deprecated "Use arrow instead")]
let efun (a: Type) (b: (a -> Type)) = arrow a b

(*| Pointwise equality of `f` and `g` on the domain `a`.

    Because of subtyping, `f` and `g` may be defined on a domain larger than
    `a`, so `feq f g` does not imply `f == g`. Use
    `FStar.FunctionalExtensionality.on_domain` to obtain equal functions. *)
let feq (#a: Type) (#b: (a -> Type)) (f g: arrow a b) = forall x. {:pattern (f x)\/(g x)} f x == g x

(*| Restricts `f` to the domain `a`: the result is a function whose maximal
    domain is `a`.

    `on_domain a f` is pointwise equal to `f`, but not provably equal to it,
    since `f` may have a larger domain. It is idempotent, and the normalizer
    reduces `on_domain a f x` to `f x`. Functions restricted this way are
    provably equal when pointwise equal; see
    `FStar.FunctionalExtensionality.extensionality`.

    Usually introduced with `FStar.FunctionalExtensionality.on_dom` or
    `FStar.FunctionalExtensionality.on`.

    Marked `inline_for_extraction`, so it adds no indirection in extracted
    code. *)
(* [on_domain a f] is habitually applied to just [a] and [f] — [feq_on_domain]
   below even has an SMT pattern on that partial application — so its arity must
   not be read off its type, whose codomain is an arrow. *)
[@@FStar.Attributes.smt_arity 3]
inline_for_extraction
val on_domain (a: Type) (#b: (a -> Type)) ([@@@strictly_positive] f: arrow a b) : Tot (arrow a b)

(*| `on_domain a f` is pointwise equal to `f`.

    Triggered automatically on `on_domain a f`. *)
val feq_on_domain (#a: Type) (#b: (a -> Type)) (f: arrow a b)
    : Lemma (feq (on_domain a f) f) [SMTPat (on_domain a f)]

(*| Restricting a function twice to the same domain is the same as
    restricting it once. *)
val idempotence_on_domain (#a: Type) (#b: (a -> Type)) (f: arrow a b)
    : Lemma (on_domain a (on_domain a f) == on_domain a f) [SMTPat (on_domain a (on_domain a f))]

(*| Holds when the maximal domain of `f` is `a`, i.e. when `f` is unchanged by
    `FStar.FunctionalExtensionality.on_domain`. *)
let is_restricted (a: Type) (#b: (a -> Type)) (f: arrow a b) = on_domain a f == f

(*| The type of dependent functions whose maximal domain is `a` and whose
    codomain is `b`.

    Pointwise equal functions of this type are provably equal. *)
let restricted_t (a: Type) (b: (a -> Type)) = f: arrow a b {is_restricted a f}

(*| `a ^-> b` is the type of non-dependent functions whose maximal domain is
    `a`.

    Pointwise equal functions of this type are provably equal. The operator is
    right associative, like `->`. *)
unfold
let ( ^-> ) (a b: Type) = restricted_t a (fun _ -> b)

(*| Introduces a restricted dependent function from `f`.

    The same as `FStar.FunctionalExtensionality.on_domain`, at the type
    `FStar.FunctionalExtensionality.restricted_t`. *)
unfold
let on_dom (a: Type) (#b: (a -> Type)) (f: arrow a b) : restricted_t a b = on_domain a f

(*| Introduces a restricted non-dependent function from `f`, of type `a ^-> b`.

    For example, `on nat (fun x -> x + 1)` is a function of type `nat ^-> int`. *)
unfold
let on (a #b: Type) (f: (a -> Tot b)) : (a ^-> b) = on_dom a f

(**** MAIN AXIOM *)

(*| Functional extensionality: functions are pointwise equal on `a` exactly
    when their restrictions to `a` are equal.

    The main axiom of the module. Triggered automatically on `feq f g`. *)
val extensionality (a: Type) (b: (a -> Type)) (f g: arrow a b)
    : Lemma (ensures (feq #a #b f g <==> on_domain a f == on_domain a g)) [SMTPat (feq #a #b f g)]

(**** DUPLICATED FOR GHOST FUNCTIONS *)

(*| The type of ghost, dependent functions from `a` to `b`.

    The ghost counterpart of `FStar.FunctionalExtensionality.arrow`. *)
unfold
let arrow_g (a: Type) (b: (a -> Type)) = x: a -> GTot (b x)

(*| Deprecated alias of `FStar.FunctionalExtensionality.arrow_g`. *)
[@@ (deprecated "Use arrow_g instead")]
let efun_g (a: Type) (b: (a -> Type)) = arrow_g a b

(*| Pointwise equality of the ghost functions `f` and `g` on the domain `a`.

    The ghost counterpart of `FStar.FunctionalExtensionality.feq`. *)
let feq_g (#a: Type) (#b: (a -> Type)) (f g: arrow_g a b) =
  forall x. {:pattern (f x)\/(g x)} f x == g x

(*| Restricts the ghost function `f` to the domain `a`.

    The ghost counterpart of `FStar.FunctionalExtensionality.on_domain`. *)
[@@FStar.Attributes.smt_arity 3]
val on_domain_g (a: Type) (#b: (a -> Type)) (f: arrow_g a b) : Tot (arrow_g a b)

(*| `on_domain_g a f` is pointwise equal to `f`.

    Triggered automatically on `on_domain_g a f`. *)
val feq_on_domain_g (#a: Type) (#b: (a -> Type)) (f: arrow_g a b)
    : Lemma (feq_g (on_domain_g a f) f) [SMTPat (on_domain_g a f)]

(*| Restricting a ghost function twice to the same domain is the same as
    restricting it once. *)
val idempotence_on_domain_g (#a: Type) (#b: (a -> Type)) (f: arrow_g a b)
    : Lemma (on_domain_g a (on_domain_g a f) == on_domain_g a f)
      [SMTPat (on_domain_g a (on_domain_g a f))]

(*| Holds when the maximal domain of the ghost function `f` is `a`.

    The ghost counterpart of `FStar.FunctionalExtensionality.is_restricted`. *)
let is_restricted_g (a: Type) (#b: (a -> Type)) (f: arrow_g a b) = on_domain_g a f == f

(*| The type of ghost dependent functions whose maximal domain is `a`.

    The ghost counterpart of `FStar.FunctionalExtensionality.restricted_t`. *)
let restricted_g_t (a: Type) (b: (a -> Type)) = f: arrow_g a b {is_restricted_g a f}

(*| `a ^->> b` is the type of ghost non-dependent functions whose maximal
    domain is `a`. *)
unfold
let ( ^->> ) (a b: Type) = restricted_g_t a (fun _ -> b)

(*| Introduces a restricted ghost dependent function from `f`. *)
unfold
let on_dom_g (a: Type) (#b: (a -> Type)) (f: arrow_g a b) : restricted_g_t a b = on_domain_g a f

(*| Introduces a restricted ghost non-dependent function from `f`, of type
    `a ^->> b`. *)
unfold
let on_g (a #b: Type) (f: (a -> GTot b)) : (a ^->> b) = on_dom_g a f

(*| Functional extensionality for ghost functions: they are pointwise equal on
    `a` exactly when their restrictions to `a` are equal.

    Triggered automatically on `feq_g f g`. *)
val extensionality_g (a: Type) (b: (a -> Type)) (f g: arrow_g a b)
    : Lemma (ensures (feq_g #a #b f g <==> on_domain_g a f == on_domain_g a g))
      [SMTPat (feq_g #a #b f g)]

