(*
   Copyright 2008-2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: Aseem Rastogi
*)

/// A partial map, partial in the sense that selecting a key in the map may fail
///   (by returning None)

module FStar.PartialMap

(*| Abstract type of partial maps from keys of type `k` to values of type `v`.

    Selecting a key may fail: `FStar.PartialMap.sel` returns an `option v`,
    `None` for keys with no binding. Keys need decidable equality. Maps
    support extensional equality, `FStar.PartialMap.equal`. The value type is
    strictly positive, so `t` can appear in inductive type definitions.

    ```fstar
    let pm : FStar.PartialMap.t int string = FStar.PartialMap.upd (FStar.PartialMap.empty int string) 1 "one"
    let _ = assert (FStar.PartialMap.sel pm 1 == Some "one" /\ FStar.PartialMap.sel pm 2 == None)
    ``` *)
val t (k:eqtype) ([@@@strictly_positive] v:Type u#a) : Type u#a

(*| The map with no bindings: `sel (empty k v) x == None` for every `x`.

    See `FStar.PartialMap.sel_empty`. *)
val empty (k:eqtype) (v:Type) : t k v

(*| Builds a map from a function giving the optional value at every key.

    `sel (literal f) x == f x` (see `FStar.PartialMap.sel_literal`). *)
val literal (#k:eqtype) (#v:Type) (f:k -> option v) : t k v

(*| Looks up a key, returning `Some` of its value, or `None` if the key has no binding. *)
val sel (#k:eqtype) (#v:Type) (m:t k v) (x:k) : option v

(*| Binds key `x` to value `y`, replacing any previous binding of `x`.

    See `FStar.PartialMap.sel_upd` and `FStar.PartialMap.sel_upd_distinct_key`. *)
val upd (#k:eqtype) (#v:Type) (m:t k v) (x:k) (y:v) : t k v

(*| Removes the binding of key `x`, if any.

    See `FStar.PartialMap.sel_remove` and
    `FStar.PartialMap.sel_remove_distinct_key`. *)
val remove (#k:eqtype) (#v:Type) (m:t k v) (x:k) : t k v

(*| Tests whether a key has a binding: `contains m x` is `Some? (sel m x)`. *)
let contains (#k:eqtype) (#v:Type) (m:t k v) (x:k) : bool =
  Some? (sel m x)

(*| The map binding every key to the same value `y`.

    Defined as `literal (fun x -> Some y)`. *)
let const (k:eqtype) (#v:Type) (y:v) : t k v =
  literal (fun x -> Some y)

/// The reasoning principles provided by the map

(*| The empty map has no bindings: `sel (empty k v) x == None`.

    Triggered automatically on `sel (empty k v) x`. *)
val sel_empty (#k:eqtype) (v:Type) (x:k)
  : Lemma (ensures sel (empty k v) x == None)
          [SMTPat (sel (empty k v) x)]

(*| Selecting in `literal f` applies `f`: `sel (literal f) x == f x`.

    Triggered automatically on `sel (literal f) x`. *)
val sel_literal (#k:eqtype) (#v:Type) (f:k -> option v) (x:k)
  : Lemma (ensures sel (literal f) x == f x)
          [SMTPat (sel (literal f) x)]

(*| Selecting the updated key returns the new value: `sel (upd m x y) x == Some y`.

    Triggered automatically on `sel (upd m x y) x`. *)
val sel_upd (#k:eqtype) (#v:Type) (m:t k v) (x:k) (y:v)
  : Lemma (ensures sel (upd m x y) x == Some y)
          [SMTPat (sel (upd m x y) x)]

(*| Updating one key does not change the value at another: `sel (upd m x1 y) x2 == sel m x2`.

    Requires `x1 =!= x2`. Triggered automatically on `sel (upd m x1 y) x2`. *)
val sel_upd_distinct_key (#k:eqtype) (#v:Type) (m:t k v) (x1 x2:k) (y:v)
  : Lemma (requires x1 =!= x2)
          (ensures sel (upd m x1 y) x2 == sel m x2)
          [SMTPat (sel (upd m x1 y) x2)]

(*| A removed key has no binding: `sel (remove m x) x == None`.

    Triggered automatically on `sel (remove m x) x`. *)
val sel_remove (#k:eqtype) (#v:Type) (m:t k v) (x:k)
  : Lemma (ensures sel (remove m x) x == None)
          [SMTPat (sel (remove m x) x)]

(*| Removing one key does not change the value at another: `sel (remove m x1) x2 == sel m x2`.

    Requires `x1 =!= x2`. Triggered automatically on `sel (remove m x1) x2`. *)
val sel_remove_distinct_key (#k:eqtype) (#v:Type) (m:t k v) (x1 x2:k)
  : Lemma (requires x1 =!= x2)
          (ensures sel (remove m x1) x2 == sel m x2)
          [SMTPat (sel (remove m x1) x2)]

/// The map type supports extensional equality
///
/// Below are the intro and elim forms

(*| Extensional equality of partial maps: `sel` agrees at every key.

    Introduced by `FStar.PartialMap.eq_intro` and eliminated into `==` by
    `FStar.PartialMap.eq_elim`. *)
val equal (#k:eqtype) (#v:Type) (m1 m2:t k v) : prop

(*| Two maps on which `sel` agrees at every key are `FStar.PartialMap.equal`.

    Requires `forall x. sel m1 x == sel m2 x`. Triggered automatically on
    `equal m1 m2`. *)
val eq_intro (#k:eqtype) (#v:Type) (m1 m2:t k v)
  : Lemma (requires forall (x:k). sel m1 x == sel m2 x)
          (ensures equal m1 m2)
          [SMTPat (equal m1 m2)]

(*| Extensionally equal partial maps are equal: `equal m1 m2` implies `m1 == m2`.

    Triggered automatically on `equal m1 m2`, so asserting `equal m1 m2` is a
    convenient way to prove `m1 == m2`. *)
val eq_elim (#k:eqtype) (#v:Type) (m1 m2:t k v)
  : Lemma (requires equal m1 m2)
          (ensures m1 == m2)
          [SMTPat (equal m1 m2)]
