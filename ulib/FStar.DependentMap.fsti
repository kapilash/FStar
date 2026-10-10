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

module FStar.DependentMap

/// This module provides an abstract type of maps whose co-domain
/// depends on the value of each key. i.e., it is an encapsulation
/// of [x:key -> value x], where [key] supports decidable equality.
///
/// The main constructors of the type are:
///   * [create]: To create the whole map from a function
///   * [upd]: To update a map at a point
///   * [restrict]: To restrict the domain of a map
///   * [concat]: To concatenate maps by taking the union of their key spaces
///   * [rename]: To rename the keys of a map
///   * [map]: To map a function over the values of a map
///
/// The main eliminators are:
///   * [sel]: To query the map for its value at a point
///
/// The interface is specified in a style that describes the action of
/// each eliminator over each of the constructors
///
/// The map also supports an extensional equality principle.

(*| Abstract type of dependent maps: total maps from keys to values whose type depends on the key.

    `t key value` encapsulates a function `k:key -> value k`. Keys live in an
    `eqtype` (universe 0, decidable equality); values may live in any
    universe. Every key has a value, so `FStar.DependentMap.sel` never fails.
    Maps are built with `FStar.DependentMap.create`, `FStar.DependentMap.upd`,
    `FStar.DependentMap.restrict`, `FStar.DependentMap.concat`,
    `FStar.DependentMap.rename` and `FStar.DependentMap.map`, and are
    specified by the action of `sel` on each of them. Maps support
    extensional equality, `FStar.DependentMap.equal`. The value type is
    strictly positive, so `t` can appear in inductive type definitions.

    ```fstar
    let dv (b: bool) : Type0 = if b then int else string
    let dm_init (b: bool) : dv b = if b then 0 else "zero"
    let dm : FStar.DependentMap.t bool dv = FStar.DependentMap.create dm_init
    let _ = assert (FStar.DependentMap.sel (FStar.DependentMap.upd dm true 1) true == 1)
    ``` *)
val t (key: eqtype) ([@@@strictly_positive] value: (key -> Type u#v)) : Type u#v

(*| Creates a map from a function giving the value at every key.

    See `FStar.DependentMap.sel_create`. *)
val create (#key: eqtype) (#value: (key -> Tot Type)) (f: (k: key -> Tot (value k)))
    : Tot (t key value)

(*| Returns the value of a map at a key.

    Total: every key has a value. *)
val sel (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) : Tot (value k)

(*| Selecting key `k` in `create f` gives `f k`.

    Triggered automatically on `sel (create f) k`. *)
val sel_create (#key: eqtype) (#value: (key -> Tot Type)) (f: (k: key -> Tot (value k))) (k: key)
    : Lemma (ensures (sel #key #value (create f) k == f k)) [SMTPat (sel #key #value (create f) k)]

(*| Updates a map at one key, leaving the other keys unchanged.

    See `FStar.DependentMap.sel_upd_same` and
    `FStar.DependentMap.sel_upd_other`. *)
val upd (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) (v: value k)
    : Tot (t key value)

(*| Selecting the updated key returns the new value: `sel (upd m k v) k == v`.

    One of the McCarthy select/update axioms. Triggered automatically on
    `sel (upd m k v) k`. *)
val sel_upd_same (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value) (k: key) (v: value k)
    : Lemma (ensures (sel (upd m k v) k == v)) [SMTPat (sel (upd m k v) k)]

(*| Selecting a key other than the updated one returns the old value.

    Requires `k' <> k`; ensures `sel (upd m k v) k' == sel m k'`. One of the
    McCarthy select/update axioms. Triggered automatically on
    `sel (upd m k v) k'`. *)
val sel_upd_other
      (#key: eqtype)
      (#value: (key -> Tot Type))
      (m: t key value)
      (k: key)
      (v: value k)
      (k': key)
    : Lemma (requires (k' <> k))
      (ensures (sel (upd m k v) k' == sel m k'))
      [SMTPat (sel (upd m k v) k')]

(*| Extensional equality of maps: same value at every key.

    Introduced by `FStar.DependentMap.equal_intro` and eliminated into `==` by
    `FStar.DependentMap.equal_elim`. *)
val equal (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value) : prop

(*| Two maps that agree on every key are `FStar.DependentMap.equal`.

    Requires `forall k. sel m1 k == sel m2 k`. Triggered automatically on
    `equal m1 m2`. *)
val equal_intro (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value)
    : Lemma (requires (forall k. sel m1 k == sel m2 k))
      (ensures (equal m1 m2))
      [SMTPat (equal m1 m2)]

(*| `FStar.DependentMap.equal` is reflexive.

    Triggered automatically on `equal m m`. *)
val equal_refl (#key: eqtype) (#value: (key -> Tot Type)) (m: t key value)
    : Lemma (ensures (equal m m)) [SMTPat (equal m m)]

(*| Extensionally equal maps are equal: `equal m1 m2` implies `m1 == m2`.

    This also shows that `FStar.DependentMap.equal` is an equivalence
    relation. Triggered automatically on `equal m1 m2`, so asserting
    `equal m1 m2` is a convenient way to prove `m1 == m2`. *)
val equal_elim (#key: eqtype) (#value: (key -> Tot Type)) (m1 m2: t key value)
    : Lemma (requires (equal m1 m2)) (ensures (m1 == m2)) [SMTPat (equal m1 m2)]

(**** Restricting the domain of a map *)

(*| Restricts the domain of a map to the keys satisfying `p`.

    The key type of the result is the refinement `k:key{p k}`; values are
    unchanged (see `FStar.DependentMap.sel_restrict`). *)
val restrict (#key: eqtype) (#value: (key -> Tot Type)) (p: (key -> prop)) (m: t key value)
    : Tot (t (k: key{p k}) value)

(*| Restriction does not change the value at a key that is kept: `sel (restrict p m) k == sel m k`.

    Has no SMT pattern; call it explicitly. *)
val sel_restrict
      (#key: eqtype)
      (#value: (key -> Tot Type))
      (p: (key -> prop))
      (m: t key value)
      (k: key{p k})
    : Lemma (ensures (sel (restrict p m) k == sel m k))

(**** Concatenating maps *)

/// Concatenating [t k1 v1] and [t k2 v2] produces a map
/// [t (either k1 k2) (concat_value v1 v2)]
///
/// I.e., the key space varies contravariantly, to take the union of
/// the component key spaces. The co-domain is the dependent product
/// of the co-domains of the original map

(*| The value type of a concatenated map: `value1 k1` at `Inl k1` and `value2 k2` at `Inr k2`.

    Used in the type of `FStar.DependentMap.concat`. *)
let concat_value
      (#key1: eqtype)
      (value1: (key1 -> Tot Type))
      (#key2: eqtype)
      (value2: (key2 -> Tot Type))
      (k: either key1 key2)
    : Tot Type =
  match k with
  | Inl k1 -> value1 k1
  | Inr k2 -> value2 k2

(*| Combines two maps into one keyed by `either key1 key2`.

    Keys `Inl k1` are looked up in the first map and keys `Inr k2` in the
    second (see `FStar.DependentMap.sel_concat_l` and
    `FStar.DependentMap.sel_concat_r`). The value type is
    `FStar.DependentMap.concat_value`. *)
val concat
      (#key1: eqtype)
      (#value1: (key1 -> Tot (Type u#v)))
      (#key2: eqtype)
      (#value2: (key2 -> Tot (Type u#v)))
      (m1: t key1 value1)
      (m2: t key2 value2)
    : Tot (t (either key1 key2) (concat_value value1 value2))

(*| Selecting a left key in a concatenation reads the first map: `sel (concat m1 m2) (Inl k1) == sel m1 k1`.

    Has no SMT pattern; call it explicitly. *)
val sel_concat_l
      (#key1: eqtype)
      (#value1: (key1 -> Tot (Type u#v)))
      (#key2: eqtype)
      (#value2: (key2 -> Tot (Type u#v)))
      (m1: t key1 value1)
      (m2: t key2 value2)
      (k1: key1)
    : Lemma (ensures (sel (concat m1 m2) (Inl k1) == sel m1 k1))

(*| Selecting a right key in a concatenation reads the second map: `sel (concat m1 m2) (Inr k2) == sel m2 k2`.

    Has no SMT pattern; call it explicitly. *)
val sel_concat_r
      (#key1: eqtype)
      (#value1: (key1 -> Tot Type))
      (#key2: eqtype)
      (#value2: (key2 -> Tot Type))
      (m1: t key1 value1)
      (m2: t key2 value2)
      (k2: key2)
    : Lemma (ensures (sel (concat m1 m2) (Inr k2) == sel m2 k2))

(**** Renamings *)

/// Given a map from [key2] to [key1], we can revise a map from [t
/// key1 v] to a map [t key2 v], by composing the maps.

(*| The value type of a renamed map: the value type of the original map at `ren k`.

    Used in the type of `FStar.DependentMap.rename`. *)
let rename_value
      (#key1: eqtype)
      (value1: (key1 -> Tot Type))
      (#key2: eqtype)
      (ren: (key2 -> Tot key1))
      (k: key2)
    : Tot Type = value1 (ren k)

(*| Re-keys a map by precomposing it with a renaming function `ren` from new keys to old keys.

    The value at a new key `k2` is the old value at `ren k2` (see
    `FStar.DependentMap.sel_rename`). *)
val rename
      (#key1: eqtype)
      (#value1: (key1 -> Tot Type))
      (m: t key1 value1)
      (#key2: eqtype)
      (ren: (key2 -> Tot key1))
    : Tot (t key2 (rename_value value1 ren))

(*| Selecting in a renamed map reads the original map at the renamed key: `sel (rename m ren) k2 == sel m (ren k2)`.

    Has no SMT pattern; call it explicitly. *)
val sel_rename
      (#key1: eqtype)
      (#value1: (key1 -> Tot Type))
      (m: t key1 value1)
      (#key2: eqtype)
      (ren: (key2 -> Tot key1))
      (k2: key2)
    : Lemma (ensures (sel (rename m ren) k2 == sel m (ren k2)))

(**** Mapping a function over a dependent map *)

(*| Applies a dependent function `f` to every value of a map.

    The value at key `k` becomes `f k (sel m k)` (see
    `FStar.DependentMap.sel_map`). *)
val map
      (#key: eqtype)
      (#value1 #value2: (key -> Tot Type))
      (f: (k: key -> value1 k -> Tot (value2 k)))
      (m: t key value1)
    : Tot (t key value2)

(*| Selecting in a mapped map applies the function: `sel (map f m) k == f k (sel m k)`.

    Triggered automatically on `sel (map f m) k`. *)
val sel_map
      (#key: eqtype)
      (#value1 #value2: (key -> Tot Type))
      (f: (k: key -> value1 k -> Tot (value2 k)))
      (m: t key value1)
      (k: key)
    : Lemma (ensures (sel (map f m) k == f k (sel m k)))
      [SMTPat (sel #key #value2 (map #key #value1 #value2 f m) k)]

(*| Mapping commutes with update: `map f (upd m k v) == upd (map f m) k (f k v)`.

    Triggered automatically on `map f (upd m k v)`. *)
val map_upd
      (#key: eqtype)
      (#value1 #value2: (key -> Tot Type))
      (f: (k: key -> value1 k -> Tot (value2 k)))
      (m: t key value1)
      (k: key)
      (v: value1 k)
    : Lemma (ensures (map f (upd m k v) == upd (map f m) k (f k v)))
      [
        //AR: wanted to write an SMTPatOr, but gives some error
        SMTPat (map #key #value1 #value2 f (upd #key #value1 m k v))
      ]


/// We seem to miss lemmas that relate map to the other constructors,
/// including create, restrict etc.
