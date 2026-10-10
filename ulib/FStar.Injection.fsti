module FStar.Injection

open FStar.Fin
open FStar.Functions
open FStar.Tactics.Easy

(* A theory of injections. As for bijections, injections are erasable
   but there is a computational variant cinj below. *)

(*| Composition of total functions: `o g f` maps `x` to `g (f x)`.

    `FStar.Injection.oo` is the ghost variant. *)
let o #a #b #c (g : b -> Tot c) (f : a -> Tot b) : a -> Tot c = fun x -> g (f x)
(*| Composition of ghost functions: `oo g f` maps `x` to `g (f x)`.

    `FStar.Injection.o` is the total variant. *)
let oo #a #b #c (g : b -> GTot c) (f : a -> GTot b) : a -> GTot c = fun x -> g (f x)

(*| An injection from `a` to `b`: a ghost function with a proof that it is
    injective; usually written `a @~> b`.

    Fields:

    - `f`: the function from `a` to `b`.
    - `is_inj`: `f x == f y` implies `x == y`.

    The type is `erasable`, and `f` is ghost. For a computationally relevant
    version, see `FStar.Injection.cinj`. *)
noeq
[@@erasable]
type injection (a b : Type) = {
  f : a -> GTot b;

  is_inj : x:a -> y:a -> f x == f y -> x == y;
}

// Not a great symbol, but F* is limited in operator support.
(*| Notation: `a @~> b` is `FStar.Injection.injection a b`. *)
[@@erasable]
let ( @~> ) a b = injection a b

(*| Builds an injection from a function and a proof that it is injective.

    The same as the record constructor, but with implicit type arguments,
    which sometimes helps inference. *)
let mk_injection
  (#a #b : _)
  (f : a -> GTot b)
  (is_inj : (x:a -> y:a -> f x == f y -> x == y))
  : (a @~> b) =
  Mkinjection f is_inj

(*| Applies an injection to a value: `x |~> i` is `i.f x`. *)
let ( |~> ) (#a #b : Type) (x : a) (i : a `injection` b) : GTot b = i.f x

(*| The image of an injection: the values of `b` reached by `i.f`, as a
    refinement of `b` (see `FStar.Functions.image_of`). *)
let image_of (#a #b: Type) (i: a @~> b) : Type = FStar.Functions.image_of i.f

(*| The inverse of an injection, defined on its image.

    Ghost, as it is obtained classically. See `FStar.Injection.inverse_lem`
    for its specification. *)
val inverse_f (#a #b : Type) (i : a @~> b) (y : image_of i) : GTot a

(*| `FStar.Injection.inverse_f i` is a right inverse of `i.f` on the image:
    `i.f (inverse_f i y) == y`.

    Triggered automatically on `inverse_f i y`. *)
val inverse_lem (#a #b : Type) (i : a @~> b) (y : image_of i)
  : Lemma (ensures i.f (inverse_f i y) == y)
          [SMTPat (inverse_f i y)]

(*| The inverse of an injection, as an injection from its image back to `a`.

    Requires classical choice, so it is ghost. *)
let inverse (#a #b : Type) (i : a @~> b) : (image_of i @~> a) = {
  f = inverse_f i;

  is_inj = easy;
}

(*| The inverse undoes the injection: `(inverse d).f (d.f x) == x`.

    Triggered automatically on `d.f x`. *)
let lem_pat (#a #b : _) (d : a @~> b) (x : a)
  : Lemma ((inverse d).f (d.f x) == x)
          [SMTPat (d.f x)]
  = d.is_inj ((inverse d).f (d.f x)) x ()

(*| Maps a value `y` in the image of an injection back to its preimage:
    `y <~| i` applies `FStar.Injection.inverse i`.

    The caller must show `FStar.Functions.in_image i.f y`. *)
let ( <~| ) (#a #b : Type) (y : b) (i : a `injection` b{in_image i.f y}) : GTot a =
  y |~> inverse i

(*| The componentwise product of two injections, from `'a & 'b` to
    `'c & 'd`. *)
let inj_prod (i1 : 'a @~> 'c) (i2 : 'b @~> 'd) : ('a & 'b @~> 'c & 'd) =
{
  f = (fun (a,b) -> (i1.f a, i2.f b));
  is_inj = easy;
}

(*| The componentwise sum of two injections, from `either 'a 'b` to
    `either 'c 'd`. *)
let inj_either (i1 : 'a @~> 'c) (i2 : 'b @~> 'd) : (either 'a 'b @~> either 'c 'd) =
{
  f = (function | Inl a -> Inl (i1.f a) | Inr b -> Inr (i2.f b));
  is_inj = easy;
}

(*| Composition of injections: from `'a @~> 'b` and `'b @~> 'c`, an injection
    `'a @~> 'c`. *)
let inj_comp (i1 : 'a @~> 'b) (i2 : 'b @~> 'c) : ('a @~> 'c) =
{
  f = i2.f `oo` i1.f;
  is_inj = easy;
}

(* Computationally relevant injections *)
(*| A computationally relevant injection: an erased `FStar.Injection.injection`
    together with an executable function that agrees with it; usually written
    `a @~>> b`.

    Fields:

    - `inj`: the underlying (erased) injection.
    - `cf`: a total function equal to `inj.f` pointwise.

    Built with `FStar.Injection.mk_cinj`. *)
inline_for_extraction noextract
noeq type cinj (a b: Type) = {
  inj: (a @~> b);
  cf: cf: (a -> b) { forall x. cf x == inj.f x };
}
(*| Notation: `a @~>> b` is `FStar.Injection.cinj a b`. *)
inline_for_extraction
let (@~>>) = cinj

(*| Composition of computationally relevant injections: from `a @~>> b` and
    `b @~>> c`, an injection `a @~>> c`. *)
inline_for_extraction noextract
let cinj_comp #a #b #c (ab: a @~>> b) (bc: b @~>> c) : (a @~>> c) =
{
  inj = ab.inj `inj_comp` bc.inj;
  cf = bc.cf `o` ab.cf;
}

(*| The componentwise sum of two computationally relevant injections, from
    `either 'a 'b` to `either 'c 'd`. *)
inline_for_extraction noextract
let cinj_either (i1 : 'a @~>> 'c) (i2 : 'b @~>> 'd) : (either 'a 'b @~>> either 'c 'd) =
{
  inj = i1.inj `inj_either` i2.inj;
  cf = (function | Inl a -> Inl (i1.cf a) | Inr b -> Inr (i2.cf b));
}

(*| Builds a computationally relevant injection from a total function `f`.

    The injectivity proof is an implicit argument filled by the tactic
    `FStar.Tactics.V2.easy_fill` when not given. *)
unfold inline_for_extraction noextract
let mk_cinj #a #b (f: a -> b) (#[Tactics.V2.easy_fill ()] is_inj: _) : (a @~>> b) =
{
  inj = { f; is_inj };
  cf = f;
}

(*| The identity computationally relevant injection on `a`. *)
inline_for_extraction noextract
let cinj_id #a : (a @~>> a) = mk_cinj id

(*| The identity injection on `a`. *)
let inj_id #a : (a @~> a) = cinj_id.inj

(*| Maps `either (fin n1) (fin n2)` into `fin (n1 + n2)`: `Inl i` goes to `i`
    and `Inr j` goes to `n1 + j`.

    The function of `FStar.Injection.cinj_nat_sum`. *)
unfold inline_for_extraction noextract
let inj_nat_sum_f (n1 n2 : nat) : either (fin n1) (fin n2) -> fin (n1 + n2) =
  function
    | Inl i -> i
    | Inr j -> n1 + j

(*| The computationally relevant injection `FStar.Injection.inj_nat_sum_f`
    from `either (fin n1) (fin n2)` into `fin (n1 + n2)`. *)
inline_for_extraction noextract
let cinj_nat_sum (n1 n2 : nat) : (either (fin n1) (fin n2) @~>> fin (n1 + n2)) =
  mk_cinj (inj_nat_sum_f n1 n2)

(*| The injection from `either (fin n1) (fin n2)` into `fin (n1 + n2)`
    mapping `Inl i` to `i` and `Inr j` to `n1 + j`.

    See `FStar.Bijection.bij_nat_sum` for the bijection. *)
let inj_nat_sum (n1 n2 : nat) : (either (fin n1) (fin n2) @~> fin (n1 + n2)) =
  (cinj_nat_sum n1 n2).inj

(*| If some injection from `fin n1` into `fin n2` exists, then `n1 <= n2`
    (the pigeonhole principle). *)
val inj_cardinal (n1 n2 : nat)
  : Lemma (requires exists (b : fin n1 @~> fin n2). True)
          (ensures n1 <= n2)
