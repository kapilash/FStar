(*
   Copyright 2008-2014 Microsoft Research

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

module FStar.Ghost

/// This module provides an erased type to abstract computationally
/// irrelevant values.
///
/// It relies on the GHOST effect defined in Prims.
///
/// [erased a] is decorated with the erasable attribute. As such,
///
///    1. The type is considered non-informative.
///
///       So, [Ghost (erased a)] can be subsumed to [Pure (erased a)]
///
///    2. The compiler extracts [erased a] to [unit]
///
///       The type is [erased a] is in a bijection with [a], as
///       witnessed by the [hide] and [reveal] function.
///
/// Importantly, computationally relevant code cannot use [reveal]
/// (it's marked [GTot])
///
/// Just like Coq's prop, it is okay to use erased types
/// freely as long as we produce an erased type.
///
/// [reveal] and [hide] are coercions: the typechecker will
/// automatically insert them when required. That is, if the type of
/// an expression is [erased X], and the expected type is NOT an
/// [erased Y], it will insert [reveal], and vice versa for [hide].

(*| The computationally irrelevant counterpart of a type `a`.

    `erased a` is in bijection with `a`, as witnessed by `FStar.Ghost.hide`
    and `FStar.Ghost.reveal`. It is marked `erasable`: it is non-informative,
    so a `Ghost` computation returning `erased a` can be used where a `Pure`
    one is expected, and it extracts to `unit`.

    The typechecker inserts `reveal` and `hide` as coercions: an expression of
    type `erased t` used where a non-erased type is expected is wrapped in
    `reveal`, and vice versa for `hide`. *)
[@@ erasable]
new
val erased ([@@@strictly_positive] a: Type u#a) : Type u#a

(*| Exposes the value hidden in an `erased a`.

    `reveal` is ghost (`GTot`), so only specifications, proofs and other ghost
    code can use the result. The inverse of `FStar.Ghost.hide`. *)
val reveal: #a: Type u#a -> erased a -> GTot a

(*| Hides a value as an `erased a`.

    `hide` is total, so computationally relevant code can create erased
    values. The inverse of `FStar.Ghost.reveal`. *)
val hide: #a: Type u#a -> a -> Tot (erased a)

(*| Hiding a revealed value gives back the original erased value.

    Triggered automatically on `FStar.Ghost.reveal x`. *)
val hide_reveal (#a: Type) (x: erased a)
    : Lemma (ensures (hide (reveal x) == x)) [SMTPat (reveal x)]

(*| Revealing a hidden value gives back the original value.

    Triggered automatically on `FStar.Ghost.hide x`. *)
val reveal_hide (#a: Type) (x: a) : Lemma (ensures (reveal (hide x) == x)) [SMTPat (hide x)]


/// The rest of this module includes several well-defined defined
/// notions. They are not trusted.

(*| Coerces a total function into a ghost function.

    `Tot` is a sub-effect of `GTot`, so this is usually done implicitly; the
    explicit coercion is occasionally useful to guide inference. *)
let tot_to_gtot (f: ('a -> Tot 'b)) (x: 'a) : GTot 'b = f x

(*| Injects a value into `erased`; an alias of `FStar.Ghost.hide`. *)
let return (#a: Type) (x: a) : erased a = hide x

(*| Sequential composition of erased values: applies `f` to the value hidden
    in `x`.

    The result stays erased, so `f` may freely use the revealed value. See
    `FStar.Ghost.op_let_At` for the `let@` notation. *)
let bind (#a #b: Type) (x: erased a) (f: (a -> Tot (erased b))) : Tot (erased b) =
  let y = reveal x in
  f y

(*| Notation for `FStar.Ghost.bind`: `let@ x = e in body` binds the value
    hidden in the erased `e`.

    ```fstar
    let sum (x y: FStar.Ghost.erased int) : FStar.Ghost.erased int =
      let open FStar.Ghost in
      let@ a = x in
      let@ b = y in
      return (a + b)
    ``` *)
unfold
let (let@) (x:erased 'a) (f:('a -> Tot (erased 'b))) : Tot (erased 'b) = bind x f

(*| Maps a ghost function over an erased value.

    The result is the erased application of `f` to the revealed argument. *)
irreducible
let elift1 (#a #b: Type) (f: (a -> GTot b)) (x: erased a)
    : Tot (y: erased b {reveal y == f (reveal x)}) =
  let@ xx = x in return (f xx)

(*| Maps a binary ghost function over two erased values. *)
irreducible
let elift2 (#a #b #c: Type) (f: (a -> b -> GTot c)) (x: erased a) (y: erased b)
    : Tot (z: erased c {reveal z == f (reveal x) (reveal y)}) =
  let@ xx = x in
  let@ yy = y in
  return (f xx yy)

(*| Maps a ternary ghost function over three erased values. *)
irreducible
let elift3
      (#a #b #c #d: Type)
      (f: (a -> b -> c -> GTot d))
      (ga: erased a)
      (gb: erased b)
      (gc: erased c)
    : Tot (gd: erased d {reveal gd == f (reveal ga) (reveal gb) (reveal gc)}) =
  let@ a = ga in
  let@ b = gb in
  let@ c = gc in
  return (f a b c)

(*| Moves a refinement on the revealed value of `r` under the `erased`
    constructor.

    The result also records that its revealed value equals `reveal r`. *)
let push_refinement #a (#p: (a -> prop)) (r: erased a {p (reveal r)})
    : erased (x: a{p x /\ x == reveal r}) =
  let x:(x: a{p x}) = reveal r in
  return x

(*| Maps a ghost function whose domain is refined by `p` over an erased value
    whose revealed value satisfies `p`. *)
irreducible
let elift1_p
      (#a #b: Type)
      (#p: (a -> prop))
      ($f: (x: a{p x} -> GTot b))
      (r: erased a {p (reveal r)})
    : Tot (z: erased b {reveal z == f (reveal r)}) =
  let x:(x: a{p x}) = reveal r in
  return (f x)

(*| Maps a binary ghost function whose second argument is refined by `p` over
    two erased values that satisfy `p`. *)
irreducible
let elift2_p
      (#a #b #c: Type)
      (#p: (a -> b -> prop))
      ($f: (xa: a -> xb: b{p xa xb} -> GTot c))
      (ra: erased a)
      (rb: erased b {p (reveal ra) (reveal rb)})
    : Tot (rc: erased c {reveal rc == f (reveal ra) (reveal rb)}) =
  let x = reveal ra in
  let y:(y: b{p x y}) = reveal rb in
  return (f x y)

(*| Like `FStar.Ghost.elift1_p`, for a function whose result is also refined.

    The refinement `q` of the codomain is not propagated to the result; only
    the equation with `f` is. *)
irreducible
let elift1_pq
      (#a #b: Type)
      (#p: (a -> prop))
      (#q: (x: a{p x} -> b -> prop))
      ($f: (x: a{p x} -> GTot (y: b{q x y})))
      (r: erased a {p (reveal r)})
    : Tot (z: erased b {reveal z == f (reveal r)}) =
  let x:(x: a{p x}) = reveal r in
  return (f x)

(*| Like `FStar.Ghost.elift2_p`, for a function whose result is also refined.

    The refinement `q` of the codomain is not propagated to the result; only
    the equation with `f` is. *)
irreducible
let elift2_pq
      (#a #b #c: Type)
      (#p: (a -> b -> prop))
      (#q: (x: a -> y: b{p x y} -> c -> prop))
      ($f: (x: a -> y: b{p x y} -> GTot (z: c{q x y z})))
      (ra: erased a)
      (rb: erased b {p (reveal ra) (reveal rb)})
    : Tot (z: erased c {reveal z == f (reveal ra) (reveal rb)}) =
  let x = reveal ra in
  let y:(y: b{p x y}) = reveal rb in
  return (f x y)

