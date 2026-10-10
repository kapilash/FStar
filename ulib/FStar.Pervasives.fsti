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
[@@"no_prelude"]
module FStar.Pervasives

(* This is a file from the core library, dependencies must be explicit *)
open Prims
open FStar.Pervasives.Native

/// This module is implicitly opened in the scope of all other
/// modules.
///
/// It provides several basic definitions in F* that are common to
/// most programs. Broadly, these include:
///
/// - Utility types and functions, like [id], [either], dependent
///   tuples, etc.
///
/// - Utility effect definitions, including [DIV] for divergence,
///   [EXN] of exceptions, [STATE_h] a template for state, and (the
///   poorly named) [ALL_h] which combines them all.
///
/// - Some utilities to control proofs, e.g., inversion of inductive
///   type definitions.
///
/// - Built-in attributes that can be used to decorate definitions and
///   trigger various kinds of special treatments for those
///   definitions.

(*| An attribute for type abbreviation signatures in interfaces: the listed
    0-based parameter positions are unused and are removed during extraction.

    Needed in particular for F# extraction, which rejects type abbreviations
    with unused type parameters. *)
val remove_unused_type_parameters : list int -> Tot unit

(*| The type of SMT quantifier triggers attached to lemmas.

    Built with `FStar.Pervasives.smt_pat` and `FStar.Pervasives.smt_pat_or`,
    usually through the `SMTPat` and `SMTPatOr` syntax. *)
type pattern : Type0 = unit

(*| A trigger on the term `x`; the target of the `SMTPat` syntax. *)
val smt_pat (#a: Type) (x: a) : Tot pattern

(*| A disjunction of conjunctions of triggers; the target of the `SMTPatOr`
    syntax.

    Nested disjunctions such as `SMTPatOr [[SMTPatOr ...]]` can be written but
    are not supported. *)
val smt_pat_or (x: list (list pattern)) : Tot pattern

(*| Types with decidable equality, in any universe.

    `Prims.eqtype` is restricted to universe 0, but some types in higher
    universes also have decidable equality. *)
type eqtype_u = a:Type{hasEq a}

(** [Lemma] is a very widely used effect abbreviation.

    It stands for a unit-returning [Ghost] computation, whose main
    value is its logical payload in proving an implication between its
    pre- and postcondition.

    [Lemma] is desugared specially. The valid forms are:

     Lemma (ensures post)
     Lemma post [SMTPat ...]
     Lemma (ensures post) [SMTPat ...]
     Lemma (ensures post) (decreases d)
     Lemma (ensures post) (decreases d) [SMTPat ...]
     Lemma (requires pre) (ensures post) (decreases d)
     Lemma (requires pre) (ensures post) [SMTPat ...]
     Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]

   and

     Lemma post    (== Lemma (ensures post))

   [Lemma (requires pre) (ensures post)] desugars to an arrow taking a
   trailing implicit [squash pre] argument -- which is what lets [pre] be
   assumed for the *well-formedness* of [post] -- and returning
   [Tot (squash post)].
*)
effect Lemma (a: Type) = Tot a

(*| Marks a proposition to be checked in its own SMT query.

    By default, all proof obligations of a verification condition are sent to
    the SMT solver in a single query. `spinoff p` is equal to `p` (see
    `FStar.Pervasives.spinoff_eq`), but is split into a separate query. *)
val spinoff (p: prop) : prop

(*| `spinoff p` is equal to `p`. *)
val spinoff_eq (p:prop) : Lemma (spinoff p == p)

(*| `spinoff p` is equivalent to `p`.

    Triggered automatically on `spinoff p`. *)
val spinoff_equiv (p:prop) : Lemma (p <==> spinoff p) [SMTPat (spinoff p)]

(*| Asserts `p`, like `assert`, but proves it in a separate SMT query. *)
val assert_spinoff (p: prop) : Pure unit (requires (spinoff p)) (ensures (fun x -> p))

(*| The polymorphic identity function. *)
unfold
let id (#a: Type) (x: a) : a = x

(*| The trivial postcondition for the `PURE` effect, which accepts every
    result. *)
unfold
let trivial_pure_post (a: Type) : a -> prop = fun _ -> True

(*| Marks the term `x` as present in the SMT context.

    Lets the solver appeal to the definition of a nullary symbol even when the
    program does not mention it, for instance for triggers. Introduce it with
    `FStar.Pervasives.intro_ambient`. *)
[@@ remove_unused_type_parameters [0; 1;]]
val ambient (#a: Type) (x: a) : prop

(*| Introduces `FStar.Pervasives.ambient x` into the SMT context. *)
val intro_ambient (#a: Type) (x: a) : Tot (squash (ambient x))

open FStar.NormSteps

///  Controlling normalization

(*| Requests full normalization: during normalization, every occurrence of
    `normalize_term e` is reduced to the full normal form of `e`.

    Logically the identity; see `FStar.Pervasives.normalize_term_spec`. Not
    extracted. *)
noextract
val normalize_term (#a: Type) (x: a) : Tot a

(*| Requests full normalization of a proposition: during normalization, every
    occurrence of `normalize p` is reduced to the full normal form of `p`.

    Logically the identity; see `FStar.Pervasives.normalize_spec`. *)
noextract
val normalize (a: prop) : prop

(*| Requests normalization of `x` using only the steps in `s`.

    Logically the identity; see `FStar.Pervasives.norm_spec`. The steps are
    defined in `FStar.NormSteps`. *)
noextract
val norm (s: list norm_step) (#a: Type) (x: a) : Tot a

(*| Proves `p` by first reducing it as much as possible, then asking the SMT
    solver to prove the result.

    Useful for facts that follow by computation, such as properties of a
    specific list. *)
val assert_norm (p: prop) : Pure unit (requires (normalize p)) (ensures (fun _ -> p))

(*| `normalize_term x` is equal to `x`.

    Brings an equation between a term and its normal form into the context. *)
val normalize_term_spec (#a: Type) (x: a) : Lemma (normalize_term #a x == x)

(*| `normalize p` is equal to `p`. *)
val normalize_spec (a: prop) : Lemma (normalize a == a)

(*| `norm s x` is equal to `x`, for any steps `s`. *)
val norm_spec (s: list norm_step) (#a: Type) (x: a) : Lemma (norm s #a x == x)

(*| Exposes the definition of an `opaque_to_smt` definition to the solver.

    Use it as `reveal_opaque name defn`, where `name` is the fully qualified
    name of `defn`, typically obtained with a `%` quotation. The definition is
    unfolded once. *)
let reveal_opaque (s: string) = norm_spec [delta_once [s]]

/// The [NDET] effect for nondeterministic, but terminating, computations

(** The effect of nondeterminism. It sits strictly between [PURE] and
    [DIV]: an [NDET] computation always terminates (the effect is marked
    [total], so recursive functions in it are still subject to a
    termination check), but it is not a mathematical function, so
    nothing relates the results of two calls to the same computation on
    the same arguments. In particular, given [f : unit -> NDET int], one
    cannot prove [let x = f () in let y = f () in x == y].

    Since [NDET] computations do terminate, they may be used at the top
    level: [let global = f ()] is fine when [f] is an [NDET]
    computation, whereas it would mask a divergent effect (and require a
    proof that the result type is inhabited) if [f] were in [DIV]. *)
total assume effect NDET

(** [Tot] computations can be silently promoted for use in an [NDET]
    context. As for [Div] below, there is deliberately no
    [GTot ~> NDET] edge.

    A lift is an edge of the effect lattice, so it names the effect
    itself, not one of its abbreviations: [PURE] is an abbreviation of
    [Tot]. *)
assume sub_effect Tot ~> NDET

(** [Ndet] is the Hoare-style counterpart of [NDET] *)
effect Ndet (a: Type) = NDET a

(** [Nd] is the instance of [NDET] with trivial pre- and postconditions *)
effect Nd (a: Type) = NDET a

/// The [DIV] effect for divergent computations

(** The effect of divergence: from a specificational perspective it is
    identical to PURE, however the specs are given a partial
    correctness interpretation. Computations with the [DIV] effect may
    not terminate. *)
assume effect Div

(** [NDET] computations can be silently promoted for use in a [Div]
    context; composed with [Tot ~> NDET] above this also gives the
    [Tot ~> Div] edge, since the lattice is closed transitively when an
    edge is added (see [Env.update_effect_lattice]).  Note that there is
    deliberately no [GTot ~> Div] edge: [Div] is not erasable, so
    admitting one would let a ghost value of an informative type flow
    into extracted code.  A [GTot] computation whose result type is
    non-informative is promoted to [Tot] first (see
    [Normalize.maybe_ghost_to_pure]) and reaches [Div] that way. *)
assume sub_effect NDET ~> Div

(** [Div] is the Hoare-style counterpart of [DIV] *)
effect DIV (a: Type) = Div a

(** [Dv] is the instance of [DIV] with trivial pre- and postconditions *)
effect Dv (a: Type) = Div a


(** We use the [EXT] effect to underspecify external system calls
    as being impure but having no observable effect on the state *)
effect EXT (a: Type) = Dv a

/// Exceptional results

(*| The result of a computation that may raise an exception or fail.

    The constructors are `V v` for a normal result, `E e` for a handleable
    exception, and `Err msg` for a fatal error. *)
noeq
type result (a: Type) =
  | V : v: a -> result a
  | E : e: exn -> result a
  | Err : msg: string -> result a

/// The [EXN] effect for computations that may raise exceptions or
/// fatal errors.
///
/// NOTE: BE WARNED, CODE IN THE [EXN] EFFECT IS ONLY CHECKED FOR
/// PARTIAL CORRECTNESS

assume effect EXN

(** We include divergence in exceptions. *)
assume sub_effect Div ~> EXN

(** A Hoare-style abbreviation for [EXN] *)
effect Exn (a: Type) = EXN a

(** A variant of [Exn] with trivial pre- and postconditions *)
effect Ex (a: Type) = EXN a

(*| Allows the SMT solver to invert the inductive type `a` without limit.

    Normally, proving that a value of an inductive type is built with one of
    its constructors uses up the bounded `ifuel` budget. When `inversion a` is
    in the context, values of `a` can be inverted regardless of `ifuel`. This
    deliberately bypasses the `ifuel` setting and can make SMT performance
    poor; introduce it with `FStar.Pervasives.allow_inversion`. *)
[@@ remove_unused_type_parameters [0]]
val inversion (a: Type) : prop

(*| Introduces `FStar.Pervasives.inversion a` into the SMT context. *)
val allow_inversion (a: Type) : Pure unit (requires True) (ensures (fun x -> inversion a))

(*| Values of `option a` can always be inverted, regardless of `ifuel`.

    Triggered automatically on `option a`. *)
val invertOption (a: Type)
    : Lemma (requires True) (ensures (forall (x: option a). None? x \/ Some? x)) [SMTPat (option a)]

(*| A value of type `a` or of type `b`: `Inl v` holds an `a` and `Inr v`
    holds a `b`. *)
type either a b =
  | Inl : v: a -> either a b
  | Inr : v: b -> either a b

(*| The first component of a dependent pair. *)
let dfst (#a: Type) (#b: a -> GTot Type) (t: dtuple2 a b)
    : Tot a
  = Mkdtuple2?._1 t

(*| The second component of a dependent pair, whose type depends on the first
    component. *)
let dsnd (#a: Type) (#b: a -> GTot Type) (t: dtuple2 a b)
    : Tot (b  (Mkdtuple2?._1 t))
  = Mkdtuple2?._2 t

(*| Dependent triples, written `x:a & y:b x & c x y`.

    The constructor is `Mkdtuple3`, with fields `_1`, `_2` and `_3`. *)
unopteq
type dtuple3 (a: Type) (b: (a -> GTot Type)) (c: (x: a -> b x -> GTot Type)) =
  | Mkdtuple3 : _1: a -> _2: b _1 -> _3: c _1 _2 -> dtuple3 a b c

(*| Dependent quadruples, written `x:a & y:b x & z:c x y & d x y z`.

    The constructor is `Mkdtuple4`, with fields `_1` to `_4`. *)
unopteq
type dtuple4
  (a: Type) (b: (x: a -> GTot Type)) (c: (x: a -> b x -> GTot Type))
  (d: (x: a -> y: b x -> z: c x y -> GTot Type))
  = | Mkdtuple4 : _1: a -> _2: b _1 -> _3: c _1 _2 -> _4: d _1 _2 _3 -> dtuple4 a b c d

(*| Dependent quintuples, written `x:a & y:b x & z:c x y & w:d x y z & e x y z w`.

    The constructor is `Mkdtuple5`, with fields `_1` to `_5`. *)
unopteq
type dtuple5
  (a: Type) (b: (x: a -> GTot Type)) (c: (x: a -> b x -> GTot Type))
  (d: (x: a -> y: b x -> z: c x y -> GTot Type))
  (e: (x: a -> y: b x -> z: c x y -> w: d x y z -> GTot Type))
  = | Mkdtuple5 : _1: a -> _2: b _1 -> _3: c _1 _2 -> _4: d _1 _2 _3 -> _5: e _1 _2 _3 _4 -> dtuple5 a b c d e

(*| Explicitly discards a value. *)
let ignore (#a: Type) (x: a) : Tot unit = ()

(*| Produces a value of any type `a` in a context where `False` is provable. *)
val false_elim (#a: Type) (u: unit{False}) : Tot a
(*| Returns `x`, at the singleton type of values equal to `x`.

    Pure and ghost inner `let` bindings are inlined when computing
    verification conditions unless their type is `unit` or their head symbol
    is `irreducible`. Binding `singleton e` instead of `e` keeps the binding.
    See `FStar.Algebra.Monoid` for an example. *)
val singleton (#a: Type) (x: a) : Tot (y: a{y == x})

(*| Weakens an `eqtype` to a `Type`.

    Useful, for example, in types of layered effect combinators, which are
    checked without subtyping. *)
unfold let eqtype_as_type (a:eqtype) : Type = a

(*| Coerces `x` from type `a` to type `b`, given a proof that `a` equals `b`.

    Usually the coercion is applied silently; occasionally it must be explicit. *)
inline_for_extraction noextract
let coerce_eq (#a:Type) (#b:Type) (_:squash (a == b)) (x:a) : b = x

(*| An attribute for `let` bindings: before extraction, the definition is
    reduced with the normalization steps `steps`.

    Similar to the `postprocess_for_extraction_with` attribute, which runs a
    tactic, but cheaper when only normalization is needed. Because it runs
    just before extraction, arguments marked `erasable` can also be erased to
    `()` during this normalization. *)
val normalize_for_extraction (steps:list norm_step) : Tot unit

(* When using [normalize_for_extraction] this flag indicates that the type
 * of the definition should also be normalized. *)
(*| An attribute used with `FStar.Pervasives.normalize_for_extraction`: the
    type of the definition is also normalized before extraction. *)
val normalize_for_extraction_type : unit
