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

(**

 @summary FStar.Map provides a polymorphic, partial map from keys to
   values, where keys support decidable equality.

 `m:Map.t key value` is a partial map from `key` to `value`

  A distinctive feature of the library is in its model of partiality.

  A map can be seen as a pair of:
    1. a total map `key -> Tot value`
    2. a set of keys that record the domain of the map

*)
module FStar.Map
module S = FStar.Set

(*| The type of partial maps from keys of an `eqtype` to values.

    A map is modeled as a pair of a total function from keys to values, read
    with `FStar.Map.sel`, and a set of keys, its domain, returned by
    `FStar.Map.domain` and tested by `FStar.Map.contains`. `sel` is defined on
    every key, including keys outside the domain. Compare maps with
    `FStar.Map.equal`, which is extensional.

    For finite maps over ordered keys with `option`-valued lookup, see
    `FStar.OrdMap`. *)
val t (key:eqtype) ([@@@strictly_positive] value:Type u#a)
  : Type u#a

(*| Looks up key `k` in map `m`.

    `sel` is total: it returns a value even for a key that is not in the
    domain of `m`. *)
val sel: #key:eqtype -> #value:Type -> t key value -> key -> Tot value

(*| Returns a map identical to `m` except that it maps `k` to `v` and has `k`
    in its domain.

    ```fstar
    let m : FStar.Map.t int string = FStar.Map.upd (FStar.Map.const "") 1 "one"
    let _ = assert (FStar.Map.sel m 1 == "one" /\ FStar.Map.sel m 2 == "")
    ``` *)
val upd: #key:eqtype -> #value:Type -> t key value -> key -> value -> Tot (t key value)

(*| The map that sends every key to `v`; its domain contains every key. *)
val const: #key:eqtype -> #value:Type -> value -> Tot (t key value)

(*| Returns the set of keys on which the partial map is defined. *)
val domain: #key:eqtype -> #value:Type -> t key value -> Tot (S.set key)

(*| Tests whether key `k` is in the domain of `m`. *)
val contains: #key:eqtype -> #value:Type -> t key value -> key -> Tot bool

(*| Combines two maps; the domain of the result is the union of the two
    domains.

    A key in the domain of `m2` is mapped to `sel m2 k`; every other key is
    mapped to `sel m1 k`. So `m2` takes precedence where the domains overlap. *)
val concat: #key:eqtype -> #value:Type -> t key value -> t key value -> Tot (t key value)

(*| Applies `f` to every value of `m`; the domain is unchanged. *)
val map_val: #val1:Type -> #val2:Type -> f:(val1 -> val2) -> #key:eqtype -> t key val1 -> Tot (t key val2)

(*| Restricts the domain of `m` to the keys that are also in `s`.

    The values returned by `FStar.Map.sel` are unchanged, including outside
    the new domain. *)
val restrict: #key:eqtype -> #value:Type -> S.set key -> t key value -> Tot (t key value)

(*| The map that sends every key to `v` and whose domain is `dom`.

    Defined as `restrict dom (const v)`. *)
let const_on (#key:eqtype) (#value:Type) (dom:S.set key) (v:value)
  : t key value
  = restrict dom (const v)


(*| The map that sends every key `k` to `f k`; its domain contains every key
    (see `FStar.Map.lemma_map_literal`). *)
val map_literal (#k:eqtype) (#v:Type) (f: k -> Tot v)
  : t k v

(* TODO: the pattern of disjoint_dom is biased towards `m1`. Why? *)
(*| The domains of `m1` and `m2` are disjoint: no key is in both.

    The quantifier is triggered only by `contains m1 x`. *)
let disjoint_dom (#key:eqtype) (#value:Type) (m1:t key value) (m2:t key value)
  = forall x.{:pattern (contains m1 x)(* ; (contains m2 x) *)} contains m1 x ==> not (contains m2 x)

(*| The domain of `m` is the set `dom`: a relational form of
    `FStar.Map.domain`. *)
let has_dom (#key:eqtype) (#value:Type) (m:t key value) (dom:S.set key)
  = forall x. contains m x <==> S.mem x dom

(* Properties about map functions *)

(*| Looking up the updated key returns the new value.

    Triggered automatically on `sel (upd m k v) k`. *)
val lemma_SelUpd1: #key:eqtype -> #value:Type -> m:t key value -> k:key -> v:value ->
                   Lemma (requires True) (ensures (sel (upd m k v) k == v))
                   [SMTPat (sel (upd m k v) k)]

(*| Updating a key does not change the value of any other key.

    Triggered automatically on `sel (upd m k2 v) k1`. *)
val lemma_SelUpd2: #key:eqtype -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                   Lemma (requires True) (ensures (k2=!=k1 ==> sel (upd m k2 v) k1 == sel m k1))
                   [SMTPat (sel (upd m k2 v) k1)]

(*| Every key of `const v` maps to `v`.

    Triggered automatically on `sel (const v) k`. *)
val lemma_SelConst: #key:eqtype -> #value:Type -> v:value -> k:key ->
                    Lemma (requires True) (ensures (sel (const v) k == v))
                    [SMTPat (sel (const v) k)]

(*| Restricting a map does not change the values returned by `sel`.

    Triggered automatically on `sel (restrict ks m) k`. *)
val lemma_SelRestrict: #key:eqtype -> #value:Type -> m:t key value -> ks:S.set key -> k:key ->
                       Lemma (requires True) (ensures (sel (restrict ks m) k == sel m k))
                       [SMTPat (sel (restrict ks m) k)]

(*| On a key in the domain of `m2`, `concat m1 m2` returns the value from `m2`.

    Triggered automatically on `sel (concat m1 m2) k`. *)
val lemma_SelConcat1: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value -> k:key ->
                      Lemma (requires True) (ensures (contains m2 k ==> sel (concat m1 m2) k==sel m2 k))
                      [SMTPat (sel (concat m1 m2) k)]

(*| On a key not in the domain of `m2`, `concat m1 m2` returns the value from
    `m1`.

    Triggered automatically on `sel (concat m1 m2) k`. *)
val lemma_SelConcat2: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value -> k:key ->
                      Lemma (requires True) (ensures (not(contains m2 k) ==> sel (concat m1 m2) k==sel m1 k))
                      [SMTPat (sel (concat m1 m2) k)]

(*| The value of a key in `map_val f m` is `f` applied to its value in `m`.

    Triggered automatically on `sel (map_val f m) k`. *)
val lemma_SelMapVal: #val1:Type -> #val2:Type -> f:(val1 -> val2) -> #key:eqtype -> m:t key val1 -> k:key ->
                     Lemma (requires True) (ensures (sel (map_val f m) k == f (sel m k)))
                     [SMTPat (sel (map_val f m) k)]

(*| `k2` is in the domain of `upd m k1 v` exactly when `k1 = k2` or `k2` is in
    the domain of `m`.

    Triggered automatically on `contains (upd m k1 v) k2`. *)
val lemma_InDomUpd1: #key:eqtype -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                     Lemma (requires True) (ensures (contains (upd m k1 v) k2 == (k1=k2 || contains m k2)))
                     [SMTPat (contains (upd m k1 v) k2)]

(*| Updating a key does not change whether any other key is in the domain.

    Triggered automatically on `contains (upd m k2 v) k1`. *)
val lemma_InDomUpd2: #key:eqtype -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                     Lemma (requires True) (ensures (k2=!=k1 ==> contains (upd m k2 v) k1 == contains m k1))
                     [SMTPat (contains (upd m k2 v) k1)]

(*| Every key is in the domain of `const v`.

    Triggered automatically on `contains (const v) k`. *)
val lemma_InDomConstMap: #key:eqtype -> #value:Type -> v:value -> k:key ->
                         Lemma (requires True) (ensures (contains (const v) k))
                         [SMTPat (contains (const v) k)]

(*| The domain of `concat m1 m2` is the union of the domains of `m1` and `m2`.

    Triggered automatically on `contains (concat m1 m2) k`. *)
val lemma_InDomConcat: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value -> k:key ->
                 Lemma (requires True) (ensures (contains (concat m1 m2) k==(contains m1 k || contains m2 k)))
                 [SMTPat (contains (concat m1 m2) k)]

(*| `map_val f m` has the same domain as `m`.

    Triggered automatically on `contains (map_val f m) k`. *)
val lemma_InMapVal: #val1:Type -> #val2:Type -> f:(val1 -> val2) -> #key:eqtype -> m:t key val1 -> k:key ->
                    Lemma (requires True) (ensures (contains (map_val f m) k == contains m k))
                    [SMTPat (contains (map_val f m) k)]

(*| A key is in the domain of `restrict ks m` exactly when it is in `ks` and in
    the domain of `m`.

    Triggered automatically on `contains (restrict ks m) k`. *)
val lemma_InDomRestrict: #key:eqtype -> #value:Type -> m:t key value -> ks:S.set key -> k:key ->
                         Lemma (requires True) (ensures (contains (restrict ks m) k == (S.mem k ks && contains m k)))
                         [SMTPat (contains (restrict ks m) k)]

(*| `contains m k` agrees with membership of `k` in `domain m`.

    Triggered automatically on either `contains m k` or `FStar.Set.mem k (domain m)`. *)
val lemma_ContainsDom: #key:eqtype -> #value:Type -> m:t key value -> k:key ->
  Lemma (requires True) (ensures (contains m k = S.mem k (domain m)))
                      [SMTPatOr[[SMTPat (contains m k)]; [SMTPat (S.mem k (domain m))]]]

(*| The domain of `upd m k v` is the domain of `m` with `k` added.

    Triggered automatically on `domain (upd m k v)`. *)
val lemma_UpdDomain : #key:eqtype -> #value:Type -> m:t key value -> k:key -> v:value ->
  Lemma (requires True)
        (ensures (S.equal (domain (upd m k v)) (S.union (domain m) (S.singleton k))))
        [SMTPat (domain (upd m k v))]

(*| `map_literal f` maps every key `k` to `f k`, and its domain is the set of
    all keys.

    Triggered automatically on `map_literal f`. *)
val lemma_map_literal (#k:eqtype) (#v:Type) (f: k -> Tot v)
  : Lemma ((forall k.{:pattern (sel (map_literal f) k)} sel (map_literal f) k == f k) /\
           domain (map_literal f) == Set.complement Set.empty)
          [SMTPat (map_literal f)]

(*** Extensional equality ***)

(*| Extensional equality of maps: `m1` and `m2` have the same domain and
    `sel m1 k == sel m2 k` for every key `k`.

    Values are compared on every key, not only on keys in the domain.
    `FStar.Map.lemma_equal_intro` and `FStar.Map.lemma_equal_elim` (both
    triggered automatically on `equal m1 m2`) make it interchangeable with
    `==`. *)
val equal (#key:eqtype) (#value:Type) (m1:t key value) (m2:t key value) : prop

(*| Proves `equal m1 m2` from the fact that the maps agree on `sel` and on
    `contains` for every key.

    Triggered automatically on `equal m1 m2`. *)
val lemma_equal_intro: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                       Lemma (requires (forall k. sel m1 k == sel m2 k /\
                                             contains m1 k = contains m2 k))
                             (ensures (equal m1 m2))
                             [SMTPat (equal m1 m2)]

(*| `equal m1 m2` holds exactly when `m1 == m2`: extensionality for maps.

    Triggered automatically on `equal m1 m2`. *)
val lemma_equal_elim: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                      Lemma (ensures (equal m1 m2 <==> m1 == m2))
                            [SMTPat (equal m1 m2)]

(*| Deprecated: equal (`==`) maps are `FStar.Map.equal`. Use
    `FStar.Map.lemma_equal_elim` instead, which states both directions.

    Triggered automatically on `equal m1 m2`. *)
[@@(deprecated "Use lemma_equal_elim instead")]
val lemma_equal_refl: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                      Lemma  (requires (m1 == m2))
                             (ensures  (equal m1 m2))
