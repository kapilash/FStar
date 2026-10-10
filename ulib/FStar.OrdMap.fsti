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
module FStar.OrdMap

open FStar.OrdSet

(* TODO (KM) : move me this should go in a common file on relations *)
(*| `total_order a f` holds when the boolean relation `f` is a non-strict
    total order on `a`: antisymmetric, transitive and total (hence also
    reflexive), like `<=` on integers.

    The same definition as `FStar.OrdSet.total_order`. *)
type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2) (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                (* totality      *)

(*| The type of comparison functions usable to order the keys of
    `FStar.OrdMap.ordmap`: boolean relations that satisfy
    `FStar.OrdMap.total_order`.

    The same definition as `FStar.OrdSet.cmp`. *)
let cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

(*| The type of finite partial maps from keys of an `eqtype`, ordered by `f`,
    to values.

    Lookup with `FStar.OrdMap.select` returns an `option`: `None` for a key
    that is not in the map. The keys form an `FStar.OrdSet.ordset`, returned by
    `FStar.OrdMap.dom`. The type does not have decidable equality; compare maps
    with `FStar.OrdMap.equal`, which is extensional.

    ```fstar
    let om : FStar.OrdMap.ordmap int string int_le =
      FStar.OrdMap.update 1 "one" FStar.OrdMap.empty
    let _ = assert (FStar.OrdMap.select 1 om == Some "one" /\ FStar.OrdMap.select 2 om == None)
    ```

    Here `int_le` is a `FStar.OrdMap.cmp int` such as `fun x y -> x <= y`.
    For maps with a total lookup function and possibly infinite domain, see
    `FStar.Map`. *)
val ordmap (k:eqtype) (v:Type u#a) (f:cmp k) : Type u#a

(*| The map with no keys (see `FStar.OrdMap.sel_empty`). *)
val empty   : #key:eqtype -> #value:Type -> #f:cmp key -> Tot (ordmap key value f)
(*| The map that sends every key in `d` to `x` and has no other keys (see
    `FStar.OrdMap.contains_const_on` and `FStar.OrdMap.select_const_on`). *)
val const_on: #key:eqtype -> #value:Type -> #f:cmp key -> d:ordset key f -> x:value -> Tot (ordmap key value f)
(*| Looks up key `k` in `m`: `Some v` if `m` maps `k` to `v`, `None` if `k` is
    not in `m`. *)
val select  : #key:eqtype -> #value:Type -> #f:cmp key -> k:key
              -> m:ordmap key value f -> Tot (option value)
(*| Returns `m` with the key `k` mapped to the value `v`, adding the key if
    necessary (see `FStar.OrdMap.sel_upd1` and `FStar.OrdMap.sel_upd2`). *)
val update  : #key:eqtype -> #value:Type -> #f:cmp key -> key -> value
              -> m:ordmap key value f -> Tot (ordmap key value f)
(*| Tests whether the key is in the map, that is, whether `select` returns
    `Some` (see `FStar.OrdMap.sel_contains`). *)
val contains: #key:eqtype -> #value:Type -> #f:cmp key -> key -> ordmap key value f
              -> Tot bool
(*| Returns the set of keys of `m` (see `FStar.OrdMap.dom_lemma`). *)
val dom     : #key:eqtype -> #value:Type -> #f:cmp key -> m:ordmap key value f ->
              Tot (ordset key f)

(*| Returns the map without the given key (see `FStar.OrdMap.sel_rem1` and
    `FStar.OrdMap.sel_rem2`). *)
val remove  : #key:eqtype -> #value:Type -> #f:cmp key -> key
              -> ordmap key value f -> Tot (ordmap key value f)
(*| Returns some binding `(k, v)` of the map, or `None` if it is empty.

    The interface specifies only `FStar.OrdMap.choose_empty` and
    `FStar.OrdMap.choose_m`, not which binding is chosen. *)
val choose  : #key:eqtype -> #value:Type -> #f:cmp key -> ordmap key value f
              -> Tot (option (key & value))

(*| Returns the number of keys of the map. *)
val size    : #key:eqtype -> #value:Type -> #f:cmp key -> ordmap key value f
              -> Tot nat

(*| Extensional equality of maps: `equal m1 m2` holds when `select` agrees on
    every key.

    `FStar.OrdMap.eq_intro` and `FStar.OrdMap.eq_lemma` (both triggered
    automatically on `equal m1 m2`) make it interchangeable with `==`. *)
val equal (#k:eqtype) (#v:Type) (#f:cmp k) (m1:ordmap k v f) (m2:ordmap k v f) : prop

(*| Proves `equal m1 m2` from the fact that `select` agrees on every key.

    Triggered automatically on `equal m1 m2`. *)
val eq_intro: #k:eqtype -> #v:Type -> #f:cmp k -> m1:ordmap k v f -> m2:ordmap k v f
              -> Lemma (requires (forall x. select #k #v #f x m1 == select #k #v #f x m2))
                      (ensures (equal m1 m2))
                 [SMTPat (equal m1 m2)]
  
(*| Maps that are `FStar.OrdMap.equal` are equal (`==`): extensionality for
    maps.

    Triggered automatically on `equal m1 m2`. *)
val eq_lemma: #k:eqtype -> #v:Type -> #f:cmp k -> m1:ordmap k v f -> m2:ordmap k v f
              -> Lemma (requires (equal m1 m2))
                      (ensures (m1 == m2))
                 [SMTPat (equal m1 m2)]

(*| Updates of two different keys commute, up to `FStar.OrdMap.equal`.

    Triggered automatically on `update x y (update x' y' m)`; the pattern fires
    on any pair of nested updates. *)
val upd_order: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> y':v
               -> m:ordmap k v f
               -> Lemma (requires (x =!= x'))
                       (ensures (equal (update #k #v #f x y (update #k #v #f x' y' m))
                                       (update #k #v #f x' y' (update #k #v #f x y m))))
                  [SMTPat (update #k #v #f x y (update #k #v #f x' y' m))] //NS:This pattern is too aggresive; it will fire for any pair of updates
                  
(*| A second update of the same key overrides the first, up to
    `FStar.OrdMap.equal`.

    Triggered automatically on `update x y (update x y' m)`; the pattern fires
    on any pair of nested updates. *)
val upd_same_k: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> y':v
                -> m:ordmap k v f
                -> Lemma (requires (True))
                        (ensures (equal (update #k #v #f x y (update #k #v #f x y' m))
					(update #k #v #f x y m)))
                   [SMTPat (update #k #v #f x y (update #k #v #f x y' m))] //NS:This pattern is too aggresive; it will fire for any pair of updates

(*| Looking up the updated key returns `Some` of the new value.

    Triggered automatically on `select x (update x y m)`. *)
val sel_upd1: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> m:ordmap k v f
              -> Lemma (requires True) (ensures select #k #v #f x
                                                (update #k #v #f x y m) == Some y)
                 [SMTPat (select #k #v #f x (update #k #v #f x y m))]

(*| Updating a key does not change the lookup of any other key.

    Triggered automatically on `select x' (update x y m)`. *)
val sel_upd2: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> m:ordmap k v f
              -> Lemma (requires True)
                       (ensures (x =!= x' ==> (select #k #v #f x' (update #k #v #f x y m)
                                               == select #k #v #f x' m)))
                 [SMTPat (select #k #v #f x' (update #k #v #f x y m))]

(*| Looking up any key in `FStar.OrdMap.empty` returns `None`.

    Triggered automatically on `select x empty`. *)
val sel_empty: #k:eqtype -> #v:Type -> #f:cmp k -> x:k
               -> Lemma (requires True)
                        (ensures (select #k #v #f x (empty #k #v #f) == None))
                  [SMTPat (select #k #v #f x (empty #k #v #f))]

(*| `contains x m` holds exactly when `select x m` is `Some`.

    Triggered automatically when both `select x m` and `contains x m` appear. *)
val sel_contains: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
                  -> Lemma (requires (True))
                           (ensures (contains #k #v #f x m = Some? (select #k #v #f x m)))
                     [SMTPat (select #k #v #f x m); SMTPat (contains #k #v #f x m)]

(*| `x'` is a key of `update x y m` exactly when `x = x'` or `x'` is a key of
    `m`.

    Triggered automatically on `contains x' (update x y m)`. *)
val contains_upd1: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k
                   -> m:ordmap k v f
                   -> Lemma (requires True)
                            (ensures (contains #k #v #f x' (update #k #v #f x y m) =
                                      (x = x' || contains #k #v #f x' m)))
                      [SMTPat (contains #k #v #f x' (update #k #v #f x y m))]

(*| Updating a key does not change whether any other key is in the map.

    Triggered automatically on `contains x' (update x y m)`. *)
val contains_upd2: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k
                   -> m:ordmap k v f
                   -> Lemma (requires True)
                            (ensures (x =!= x' ==> (contains #k #v #f x' (update #k #v #f x y m)
                                                    = contains #k #v #f x' m)))
                      [SMTPat (contains #k #v #f x' (update #k #v #f x y m))]

(*| `FStar.OrdMap.empty` contains no key.

    Triggered automatically on `contains x empty`. *)
val contains_empty: #k:eqtype -> #v:Type -> #f:cmp k -> x:k
                    -> Lemma (requires True)
                             (ensures (not (contains #k #v #f x (empty #k #v #f))))
                       [SMTPat (contains #k #v #f x (empty #k #v #f))]

(*| `x` is a key of `remove y m` exactly when it is a key of `m` and differs
    from `y`.

    Triggered automatically on `contains x (remove y m)`. *)
val contains_remove: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:k -> m:ordmap k v f
                     -> Lemma (requires True)
                              (ensures (contains #k #v #f x (remove #k #v #f y m) =
                                       (contains #k #v #f x m && not (x = y))))
                        [SMTPat (contains #k #v #f x (remove #k #v #f y m))]
                  
(*| Removing a key that is not in the map leaves it unchanged, up to
    `FStar.OrdMap.equal`.

    Triggered automatically on `remove x m`. *)
val eq_remove: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
              -> Lemma (requires (not (contains #k #v #f x m)))
                      (ensures (equal m (remove #k #v #f x m)))
                 [SMTPat (remove #k #v #f x m)]

(*| `choose empty` is `None`.

    Triggered automatically on `choose empty`. *)
val choose_empty: #k:eqtype -> #v:Type -> #f:cmp k
                 -> Lemma (requires True) (ensures (None? (choose #k #v #f
                                                             (empty #k #v #f))))
                    [SMTPat (choose #k #v #f (empty #k #v #f))]

(*| On a map that is not equal to `FStar.OrdMap.empty`, `choose m` returns
    `Some (k, v)` for a binding of `m`, and `m` is equal to `remove k m`
    updated with `k` mapped to `v`.

    Triggered automatically on `choose m`. *)
val choose_m: #k:eqtype -> #v:Type -> #f:cmp k -> m:ordmap k v f
             -> Lemma (requires (~ (equal m (empty #k #v #f))))
                     (ensures (Some? (choose #k #v #f m) /\
                                (select #k #v #f (fst (Some?.v (choose #k #v #f m))) m ==
                                 Some (snd (Some?.v (choose #k #v #f m)))) /\
                                (equal m (update #k #v #f (fst (Some?.v (choose #k #v #f m)))
                                                     (snd (Some?.v (choose #k #v #f m)))
                                                     (remove #k #v #f (fst (Some?.v (choose #k #v #f m))) m)))))
                [SMTPat (choose #k #v #f m)]

(*| `FStar.OrdMap.empty` has size 0.

    Triggered automatically on `size empty`. *)
val size_empty: #k:eqtype -> #v:Type -> #f:cmp k
                -> Lemma (requires True)
                         (ensures (size #k #v #f (empty #k #v #f) = 0))
                   [SMTPat (size #k #v #f (empty #k #v #f))]
                   
(*| Removing a key of the map decreases its size by one.

    Triggered automatically on `size (remove y m)`. *)
val size_remove: #k:eqtype -> #v:Type -> #f:cmp k -> y:k -> m:ordmap k v f
                -> Lemma (requires (contains #k #v #f y m))
                         (ensures (size #k #v #f m = size #k #v #f (remove #k #v #f y m) + 1))
                   [SMTPat (size #k #v #f (remove #k #v #f y m))]

(*| `x` is a key of `m` exactly when it is a member of `dom m`.

    Triggered automatically on `FStar.OrdSet.mem x (dom m)`. *)
val dom_lemma: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
               -> Lemma (requires True)
                        (ensures (contains #k #v #f x m <==>
                                  OrdSet.mem #k #f x (dom #k #v #f m)))
                  [SMTPat (mem #k #f x (dom #k #v #f m))]

(*| The keys of `const_on d x` are exactly the members of `d`.

    Triggered automatically on `contains y (const_on d x)`. *)
val contains_const_on: #k:eqtype -> #v:Type -> #f:cmp k -> d:ordset k f -> x:v -> y:k
                  -> Lemma (requires (True))
                           (ensures (mem y d = contains y (const_on d x)))
                                    //(contains y (const_on d x) ==> Some?.v (select p w) = x)))
                     [SMTPat (contains #k #v #f y (const_on #k #v #f d x))]
                     
(*| Every member of `d` is a key of `const_on d x` mapped to `x`.

    Triggered automatically on `select y (const_on d x)`. *)
val select_const_on: #k:eqtype -> #v:Type -> #f:cmp k -> d:ordset k f -> x:v -> y:k
                     -> Lemma (requires True)
                             (ensures (mem y d ==> (contains y (const_on d x) /\ Some?.v (select y (const_on d x)) == x)))
                    [SMTPat (select #k #v #f y (const_on #k #v #f d x))]

(*| Looking up a removed key returns `None`.

    Triggered automatically on `select x (remove x m)`. *)
val sel_rem1: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
              -> Lemma (requires True) (ensures select #k #v #f x
                                                (remove #k #v #f x m) == None)
                 [SMTPat (select #k #v #f x (remove #k #v #f x m))]

(*| Removing a key does not change the lookup of any other key.

    Triggered automatically on `select x' (remove x m)`. *)
val sel_rem2: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> x':k -> m:ordmap k v f
              -> Lemma (requires True) (ensures (x =!= x' ==>
                                                 select #k #v #f x'
                                                 (remove #k #v #f x m) == select #k #v #f x' m))
                 [SMTPat (select #k #v #f x' (remove #k #v #f x m))]

(*| Updating a key and removing a different key commute, up to
    `FStar.OrdMap.equal`.

    Triggered automatically on `update x y (remove x' m)`. *)
val rem_upd: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> m:ordmap k v f
             -> Lemma (requires (True)) (ensures (x =!= x' ==>
                                                  equal (update #k #v #f x y (remove #k #v #f x' m))
                                                        (remove #k #v #f x' (update #k #v #f x y m))))
                [SMTPat (update #k #v #f x y (remove #k #v #f x' m))]
