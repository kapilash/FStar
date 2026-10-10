(*
   Copyright 2008-2021 John Li, Jay Lorch, Rustan Leino, Alex Summers,
   Dan Rosen, Nikhil Swamy, Microsoft Research, and contributors to
   the Dafny Project

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Includes material from the Dafny project
   (https://github.com/dafny-lang/dafny) which carries this license
   information:

     Created 9 February 2008 by Rustan Leino.
     Converted to Boogie 2 on 28 June 2008.
     Edited sequence axioms 20 October 2009 by Alex Summers.
     Modified 2014 by Dan Rosen.
     Copyright (c) 2008-2014, Microsoft.
     Copyright by the contributors to the Dafny Project
     SPDX-License-Identifier: MIT
*)

(**
This module declares a type and functions used for modeling
finite maps as they're modeled in Dafny.

@summary Type and functions for modeling finite maps
*)
module FStar.FiniteMap.Base

open FStar.FunctionalExtensionality
module FSet = FStar.FiniteSet.Base

(*| The type of total functions from keys of type `a` to `option b` that
    return `Some` exactly on the keys in the finite set `s`.

    It is the representation of a map's contents:
    `FStar.FiniteMap.Base.elements m` has type `setfun_t a b (domain m)`,
    and `FStar.FiniteMap.Base.glue` builds a map from such a function. *)
type setfun_t (a: eqtype)
              (b: Type u#b)
              (s: FSet.set a) =
   f: (a ^-> option b){forall (key: a). FSet.mem key s == Some? (f key)}

(*| The type of finite maps from keys of an `eqtype` `a` to values of any
    type `b`, modeled on Dafny's `Map U V`.

    The type is abstract. A map has a finite domain,
    `FStar.FiniteMap.Base.domain`, and contents,
    `FStar.FiniteMap.Base.elements`. Properties of the operations are stated
    by the `_fact` propositions of this module, collected in
    `FStar.FiniteMap.Base.all_finite_map_facts`. Use
    `FStar.FiniteMap.Base.equal` and
    `FStar.FiniteMap.Base.map_extensionality_fact` to prove two maps equal.

    This module is independent of `FStar.Map`, whose maps are total. *)
val map (a: eqtype) ([@@@ strictly_positive] b: Type u#b)
  : Type u#b

(**
  We translate each Dafny sequence function prefixed with `Map#`
  into an F* function.
**)

/// We represent the Dafny function `Map#Domain` with `domain`:
///
/// function Map#Domain<U,V>(Map U V) : Set U;

(*| Returns the finite set of keys of a map (Dafny's `Map#Domain`). *)
val domain (#a: eqtype) (#b: Type u#b) (m: map a b)
  : FSet.set a

/// We represent the Dafny function `Map#Elements` with `elements`:
///
/// function Map#Elements<U,V>(Map U V) : [U]V;

(*| Returns the contents of a map as a function that gives `Some v` for a
    key in the domain bound to `v`, and `None` for every other key (Dafny's
    `Map#Elements`).

    For a key known to be in the map, `FStar.FiniteMap.Base.lookup` returns
    the value directly. *)
val elements (#a: eqtype) (#b: Type u#b) (m: map a b)
  : setfun_t a b (domain m)

/// We represent the Dafny operator `in` on maps with `mem`:

(*| Tests whether `key` is in the domain of `m` (Dafny's `key in m`).

    See also `FStar.FiniteMap.Base.notin`. *)
let mem (#a: eqtype) (#b: Type u#b) (key: a) (m: map a b) =
  FSet.mem key (domain m)

/// We can convert a map to a list of pairs with `map_as_list`:

(*| Tests whether some pair in the list `items` has `key` as its first
    component.

    Used to specify `FStar.FiniteMap.Base.map_as_list`. *)
let rec key_in_item_list (#a: eqtype) (#b: Type u#b) (key: a) (items: list (a & b)) : bool =
  match items with
  | [] -> false
  | (k, v) :: tl -> key = k || key_in_item_list key tl

(*| Holds when no key occurs as the first component of two pairs in the list
    `items`.

    Used to specify `FStar.FiniteMap.Base.map_as_list`. *)
let rec item_list_doesnt_repeat_keys (#a: eqtype) (#b: Type u#b) (items: list (a & b)) : bool =
  match items with
  | [] -> true
  | (k, v) :: tl -> not (key_in_item_list k tl) && item_list_doesnt_repeat_keys tl

(*| Returns, in ghost code, the key-value pairs of a map as a list, in an
    unspecified order.

    Each key of the map occurs in exactly one pair, and no other key occurs. *)
val map_as_list (#a: eqtype) (#b: Type u#b) (m: map a b)
  : GTot (items: list (a & b){item_list_doesnt_repeat_keys items /\ (forall key. key_in_item_list key items <==> mem key m)})

/// We represent the Dafny operator [] on maps with `lookup`:

(*| Returns the value bound to `key` in `m` (Dafny's `m[key]`).

    The caller must prove `mem key m`. The result is the value inside
    `FStar.FiniteMap.Base.elements m key`. *)
let lookup (#a: eqtype) (#b: Type u#b) (key: a) (m: map a b{mem key m})
  : b =
  Some?.v ((elements m) key)

/// We represent the Dafny function `Map#Card` with `cardinality`:
///
/// function Map#Card<U,V>(Map U V) : int;

(*| Returns, in ghost code, the number of keys of a map (Dafny's
    `Map#Card`).

    `FStar.FiniteMap.Base.map_cardinality_matches_domain_fact` states that
    it is the cardinality of the domain. *)
val cardinality (#a: eqtype) (#b: Type u#b) (m: map a b)
  : GTot nat

/// We represent the Dafny function `Map#Values` with `values`:
///
/// function Map#Values<U,V>(Map U V) : Set V;

(*| Returns, in ghost code, the set of values of a map, as a predicate on
    values (Dafny's `Map#Values`).

    It is a predicate rather than a `FStar.FiniteSet.Base.set` because
    values need not have decidable equality.
    `FStar.FiniteMap.Base.values_contains_fact` characterizes it. *)
val values (#a: eqtype) (#b: Type u#b) (m: map a b)
  : GTot (b -> prop)

/// We represent the Dafny function `Map#Items` with `items`:
///
/// function Map#Items<U,V>(Map U V) : Set Box;

(*| Returns, in ghost code, the set of key-value pairs of a map, as a
    predicate on pairs (Dafny's `Map#Items`).

    `FStar.FiniteMap.Base.items_contains_fact` characterizes it. *)
val items (#a: eqtype) (#b: Type u#b) (m: map a b)
  : GTot ((a & b) -> prop)

/// We represent the Dafny function `Map#Empty` with `emptymap`:
///
/// function Map#Empty<U, V>(): Map U V;

(*| The map with an empty domain (Dafny's `Map#Empty`). *)
val emptymap (#a: eqtype) (#b: Type u#b)
  : map a b

/// We represent the Dafny function `Map#Glue` with `glue`.
///
/// function Map#Glue<U, V>([U]bool, [U]V, Ty): Map U V;

(*| Builds the map whose domain is `keys` and whose contents are `f`
    (Dafny's `Map#Glue`).

    See `FStar.FiniteMap.Base.glue_domain_fact` and
    `FStar.FiniteMap.Base.glue_elements_fact`. *)
val glue (#a: eqtype) (#b: Type u#b) (keys: FSet.set a) (f: setfun_t a b keys)
  : map a b

/// We represent the Dafny function `Map#Build` with `insert`:
///
/// function Map#Build<U, V>(Map U V, U, V): Map U V;

(*| Returns `m` with `k` bound to `v`, replacing any previous binding of `k`
    (Dafny's `Map#Build`).

    See `FStar.FiniteMap.Base.insert_elements_fact` and the cardinality
    facts `FStar.FiniteMap.Base.insert_member_cardinality_fact` and
    `FStar.FiniteMap.Base.insert_nonmember_cardinality_fact`. *)
val insert (#a: eqtype) (#b: Type u#b) (k: a) (v: b) (m: map a b)
  : map a b

/// We represent the Dafny function `Map#Merge` with `merge`:
///
/// function Map#Merge<U, V>(Map U V, Map U V): Map U V;

(*| Returns the union of two maps; on a key in both domains, the value from
    `m2` wins (Dafny's `Map#Merge`).

    See `FStar.FiniteMap.Base.merge_domain_is_union_fact` and
    `FStar.FiniteMap.Base.merge_element_fact`. *)
val merge (#a: eqtype) (#b: Type u#b) (m1: map a b) (m2: map a b)
  : map a b

/// We represent the Dafny function `Map#Subtract` with `subtract`:
///
/// function Map#Subtract<U, V>(Map U V, Set U): Map U V;

(*| Returns `m` without the keys in the finite set `s` (Dafny's
    `Map#Subtract`).

    See `FStar.FiniteMap.Base.subtract_domain_fact` and
    `FStar.FiniteMap.Base.subtract_element_fact`. *)
val subtract (#a: eqtype) (#b: Type u#b) (m: map a b) (s: FSet.set a)
  : map a b

/// We represent the Dafny function `Map#Equal` with `equal`:
///
/// function Map#Equal<U, V>(Map U V, Map U V): bool;

(*| Holds when two maps have the same domain and the same value for each key
    (Dafny's `Map#Equal`).

    `FStar.FiniteMap.Base.map_equal_fact` characterizes it and
    `FStar.FiniteMap.Base.map_extensionality_fact` turns it into `m1 == m2`. *)
val equal (#a: eqtype) (#b: Type u#b) (m1: map a b) (m2: map a b)
  : prop

/// We represent the Dafny function `Map#Disjoint` with `disjoint`:
///
/// function Map#Disjoint<U, V>(Map U V, Map U V): bool;

(*| Holds when two maps have no key in common (Dafny's `Map#Disjoint`).

    `FStar.FiniteMap.Base.disjoint_fact` characterizes it. *)
val disjoint (#a: eqtype) (#b: Type u#b) (m1: map a b) (m2: map a b)
  : prop

/// We represent the Dafny choice operator by `choose`:
///
/// var x: T :| x in s;

(*| Returns, in ghost code, some key of a nonempty map (Dafny's
    `x :| x in m`).

    The caller must prove that `m` has a key. Which key is returned is
    unspecified. *)
val choose (#a: eqtype) (#b: Type u#b) (m: map a b{exists key. mem key m})
  : GTot (key: a{mem key m})

/// We add the utility functions `remove` and `notin`:

(*| Returns `m` without the key `key`; defined as
    `subtract m (FStar.FiniteSet.Base.singleton key)`. *)
let remove (#a: eqtype) (#b: Type u#b) (key: a) (m: map a b)
  : map a b =
  subtract m (FSet.singleton key)

(*| Tests whether `key` is not in the domain of `m`; the negation of
    `FStar.FiniteMap.Base.mem`. *)
let notin (#a: eqtype) (#b: Type u#b) (key: a) (m: map a b)
  : bool =
  not (mem key m)

(**
  We translate each finite map axiom from the Dafny prelude into an F*
  predicate ending in `_fact`.
**)

/// We don't need the following axiom since we return a nat from cardinality:
/// 
/// axiom (forall<U,V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));

/// We represent the following Dafny axiom with `cardinality_zero_iff_empty_fact`:
/// 
/// axiom (forall<U, V> m: Map U V ::
///  { Map#Card(m) }
///  Map#Card(m) == 0 <==> m == Map#Empty());

(*| States that a map has cardinality 0 exactly when it is
    `FStar.FiniteMap.Base.emptymap`.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `cardinality m`. *)
let cardinality_zero_iff_empty_fact =
  forall (a: eqtype) (b:Type u#b) (m: map a b).{:pattern cardinality m}
    cardinality m = 0 <==> m == emptymap

/// We represent the following Dafny axiom with `empty_or_domain_occupied_fact`:
///
/// axiom (forall<U, V> m: Map U V ::
///  { Map#Domain(m) }
///  m == Map#Empty() || (exists k: U :: Map#Domain(m)[k]));

(*| States that a map is either `FStar.FiniteMap.Base.emptymap` or has a
    key.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `domain m`. *)
let empty_or_domain_occupied_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b).{:pattern domain m}
    m == emptymap \/ (exists k.{:pattern mem k m} mem k m)

/// We represent the following Dafny axiom with `empty_or_values_occupied_fact`:
///
/// axiom (forall<U, V> m: Map U V ::
///  { Map#Values(m) }
///  m == Map#Empty() || (exists v: V :: Map#Values(m)[v]));

(*| States that a map is either `FStar.FiniteMap.Base.emptymap` or has a
    value in `values m`.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `values m`. *)
let empty_or_values_occupied_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b).{:pattern values m}
    m == emptymap \/ (exists v. {:pattern values m v } (values m) v)

/// We represent the following Dafny axiom with `empty_or_items_occupied_fact`:
///
/// axiom (forall<U, V> m: Map U V ::
///  { Map#Items(m) }
///  m == Map#Empty() || (exists k, v: Box :: Map#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

(*| States that a map is either `FStar.FiniteMap.Base.emptymap` or has an
    item in `items m`.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `items m`. *)
let empty_or_items_occupied_fact =
  forall (a: eqtype) (b:Type u#b) (m: map a b).{:pattern items m}
    m == emptymap \/ (exists item. {:pattern items m item } (items m) item)

/// We represent the following Dafny axiom with `map_cardinality_matches_domain_fact`:
///
/// axiom (forall<U, V> m: Map U V ::
///  { Set#Card(Map#Domain(m)) }
///  Set#Card(Map#Domain(m)) == Map#Card(m));

(*| States that the cardinality of a map is the cardinality of its domain.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `FStar.FiniteSet.Base.cardinality (domain m)`. *)
let map_cardinality_matches_domain_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b).{:pattern FSet.cardinality (domain m)}
    FSet.cardinality (domain m) = cardinality m
    
/// We don't use the following Dafny axioms, which would require
/// treating the values and items as finite sets, which we can't do
/// because we want to allow non-eqtypes as values.
///
/// axiom (forall<U, V> m: Map U V ::
///  { Set#Card(Map#Values(m)) }
///  Set#Card(Map#Values(m)) <= Map#Card(m));
/// axiom (forall<U, V> m: Map U V ::
///  { Set#Card(Map#Items(m)) }
///  Set#Card(Map#Items(m)) == Map#Card(m));

/// We represent the following Dafny axiom with `values_contains_fact`:
///
/// axiom (forall<U,V> m: Map U V, v: V :: { Map#Values(m)[v] }
///  Map#Values(m)[v] ==
/// 	(exists u: U :: { Map#Domain(m)[u] } { Map#Elements(m)[u] }
///          Map#Domain(m)[u] &&
///          v == Map#Elements(m)[u]));

(*| States that `v` is in `values m` exactly when some key in the domain of
    `m` is bound to `v`.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `values m v`. *)
let values_contains_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (v: b).{:pattern (values m) v}
    (values m) v <==>
       (exists (u: a).{:pattern FSet.mem u (domain m) \/ ((elements m) u)}
          FSet.mem u (domain m) /\ (elements m) u == Some v)

/// We represent the following Dafny axiom with `items_contains_fact`:
///
/// axiom (forall m: Map Box Box, item: Box :: { Map#Items(m)[item] }
///  Map#Items(m)[item] <==>
///    Map#Domain(m)[_System.Tuple2._0($Unbox(item))] &&
///    Map#Elements(m)[_System.Tuple2._0($Unbox(item))] == _System.Tuple2._1($Unbox(item)));

(*| States that the pair `item` is in `items m` exactly when its first
    component is in the domain of `m` and bound to its second component.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `items m item`. *)
let items_contains_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (item: a & b).{:pattern (items m) item}
    (items m) item <==>
        FSet.mem (fst item) (domain m)
      /\ (elements m) (fst item) == Some (snd item)

/// We represent the following Dafny axiom with `empty_domain_empty_fact`:
///
/// axiom (forall<U, V> u: U ::
///        { Map#Domain(Map#Empty(): Map U V)[u] }
///        !Map#Domain(Map#Empty(): Map U V)[u]);

(*| States that no key is in the domain of `FStar.FiniteMap.Base.emptymap`.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `FStar.FiniteSet.Base.mem u (domain emptymap)`. *)
let empty_domain_empty_fact =
  forall (a: eqtype) (b: Type u#b) (u: a).{:pattern FSet.mem u (domain (emptymap #a #b))}
    not (FSet.mem u (domain (emptymap #a #b)))

/// We represent the following Dafny axiom with `glue_domain_fact`:
///
/// axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
///  { Map#Domain(Map#Glue(a, b, t)) }
///  Map#Domain(Map#Glue(a, b, t)) == a);

(*| States that the domain of `glue keys f` is `keys`.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `domain (glue keys f)`. *)
let glue_domain_fact =
  forall (a: eqtype) (b: Type u#b) (keys: FSet.set a) (f: setfun_t a b keys).{:pattern domain (glue keys f)}
    domain (glue keys f) == keys

/// We represent the following Dafny axiom with `glue_elements_fact`.
/// But we have to change it because our version of `Map#Elements`
/// returns a map to an optional value.
///
/// axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
///  { Map#Elements(Map#Glue(a, b, t)) }
///  Map#Elements(Map#Glue(a, b, t)) == b);

(*| States that `glue keys f` has domain `keys` and contents `f`.

    Unlike Dafny's axiom it also restates the domain, since `elements`
    returns optional values.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `elements (glue keys f)`. *)
let glue_elements_fact =
  forall (a: eqtype) (b: Type u#b) (keys: FSet.set a) (f: setfun_t a b keys).{:pattern elements (glue keys f)}
      domain (glue keys f) == keys
    /\ elements (glue keys f) == f

/// We don't need the following Dafny axiom since the type of `glue` implies it:
///
/// axiom (forall a: [Box]bool, b: [Box]Box, t0, t1: Ty ::
///  { Map#Glue(a, b, TMap(t0, t1)) }
///  // In the following line, no trigger needed, since the quantifier only gets used in negative contexts
///  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
///  ==>
///  $Is(Map#Glue(a, b, TMap(t0, t1)), TMap(t0, t1)));

/// We represent the following Dafny axiom with `insert_elements_fact`:
///
/// axiom (forall<U, V> m: Map U V, u: U, u': U, v: V ::
///  { Map#Domain(Map#Build(m, u, v))[u'] } { Map#Elements(Map#Build(m, u, v))[u'] }
///  (u' == u ==> Map#Domain(Map#Build(m, u, v))[u'] &&
///               Map#Elements(Map#Build(m, u, v))[u'] == v) &&
///  (u' != u ==> Map#Domain(Map#Build(m, u, v))[u'] == Map#Domain(m)[u'] &&
///               Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));

(*| States how `insert key value m` looks up a key `key'`: `key` is in the
    domain and bound to `value`, and any other key has the same membership
    and contents as in `m`.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on either `FStar.FiniteSet.Base.mem key' (domain (insert key value m))`
    or `elements (insert key value m) key'`. *)
let insert_elements_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (key: a) (key': a) (value: b).
    {:pattern FSet.mem key' (domain (insert key value m)) \/ ((elements (insert key value m)) key')}
      (key' = key ==>   FSet.mem key' (domain (insert key value m))
                     /\ (elements (insert key value m)) key' == Some value)
    /\ (key' <> key ==>   FSet.mem key' (domain (insert key value m)) = FSet.mem key' (domain m)
                     /\ (elements (insert key value m)) key' == (elements m) key')

/// We represent the following Dafny axiom with `insert_member_cardinality_fact`:
///
/// axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }
///  Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));

(*| States that inserting a key already in the domain leaves the cardinality
    unchanged.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `cardinality (insert key value m)`. *)
let insert_member_cardinality_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (key: a) (value: b).{:pattern cardinality (insert key value m)}
    FSet.mem key (domain m) ==> cardinality (insert key value m) = cardinality m

/// We represent the following Dafny axiom with `insert_nonmember_cardinality_fact`:
///
/// axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }
///  !Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

(*| States that inserting a key not in the domain increases the cardinality
    by 1.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `cardinality (insert key value m)`. *)
let insert_nonmember_cardinality_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (key: a) (value: b).{:pattern cardinality (insert key value m)}
    not (FSet.mem key (domain m)) ==> cardinality (insert key value m) = cardinality m + 1

/// We represent the following Dafny axiom with `merge_domain_is_union_fact`:
///
/// axiom (forall<U, V> m: Map U V, n: Map U V ::
///  { Map#Domain(Map#Merge(m, n)) }
///  Map#Domain(Map#Merge(m, n)) == Set#Union(Map#Domain(m), Map#Domain(n)));

(*| States that the domain of `merge m1 m2` is the union of the domains.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `domain (merge m1 m2)`. *)
let merge_domain_is_union_fact =
  forall (a: eqtype) (b: Type u#b) (m1: map a b) (m2: map a b).{:pattern domain (merge m1 m2)}
    domain (merge m1 m2) == FSet.union (domain m1) (domain m2)

/// We represent the following Dafny axiom with `merge_element_fact`:
///
/// axiom (forall<U, V> m: Map U V, n: Map U V, u: U ::
///  { Map#Elements(Map#Merge(m, n))[u] }
///  Map#Domain(Map#Merge(m, n))[u] ==>
///    (!Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(m)[u]) &&
///    (Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(n)[u]));

(*| States the contents of `merge m1 m2` at a key in its domain: those of
    `m2` if the key is in the domain of `m2`, and otherwise those of `m1`,
    whose domain then contains the key.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `elements (merge m1 m2) key`. *)
let merge_element_fact =
  forall (a: eqtype) (b: Type u#b) (m1: map a b) (m2: map a b) (key: a).{:pattern (elements (merge m1 m2)) key}
    FSet.mem key (domain (merge m1 m2)) ==>
        (not (FSet.mem key (domain m2)) ==> FSet.mem key (domain m1) /\ (elements (merge m1 m2)) key == (elements m1) key)
      /\ (FSet.mem key (domain m2) ==> (elements (merge m1 m2)) key == (elements m2) key)

/// We represent the following Dafny axiom with `subtract_domain_fact`:
///
/// axiom (forall<U, V> m: Map U V, s: Set U ::
///  { Map#Domain(Map#Subtract(m, s)) }
///  Map#Domain(Map#Subtract(m, s)) == Set#Difference(Map#Domain(m), s));

(*| States that the domain of `subtract m s` is the domain of `m` minus `s`.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `domain (subtract m s)`. *)
let subtract_domain_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (s: FSet.set a).{:pattern domain (subtract m s)}
    domain (subtract m s) == FSet.difference (domain m) s

/// We represent the following Dafny axiom with `subtract_element_fact`:
///
/// axiom (forall<U, V> m: Map U V, s: Set U, u: U ::
///  { Map#Elements(Map#Subtract(m, s))[u] }
///  Map#Domain(Map#Subtract(m, s))[u] ==>
///    Map#Elements(Map#Subtract(m, s))[u] == Map#Elements(m)[u]);

(*| States that at a key in the domain of `subtract m s`, the key is in the
    domain of `m` and the contents are those of `m`.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `elements (subtract m s) key`. *)
let subtract_element_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (s: FSet.set a) (key: a).{:pattern (elements (subtract m s)) key}
    FSet.mem key (domain (subtract m s)) ==> FSet.mem key (domain m) /\ (elements (subtract m s)) key == (elements m) key

/// We represent the following Dafny axiom with `map_equal_fact`:
///
/// axiom (forall<U, V> m: Map U V, m': Map U V::
///  { Map#Equal(m, m') }
///    Map#Equal(m, m') <==> (forall u : U :: Map#Domain(m)[u] == Map#Domain(m')[u]) &&
///                          (forall u : U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));

(*| Characterizes `FStar.FiniteMap.Base.equal`: `equal m1 m2` holds exactly
    when the maps have the same domain and the same contents at each key of
    the domain.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `equal m1 m2`. *)
let map_equal_fact =
  forall (a: eqtype) (b: Type u#b) (m1: map a b) (m2: map a b).{:pattern equal m1 m2}
    equal m1 m2 <==>   (forall key. FSet.mem key (domain m1) = FSet.mem key (domain m2))
                   /\ (forall key. FSet.mem key (domain m1) ==> (elements m1) key == (elements m2) key)

/// We represent the following Dafny axiom with `map_extensionality_fact`:
///
/// axiom (forall<U, V> m: Map U V, m': Map U V::
///  { Map#Equal(m, m') }
///    Map#Equal(m, m') ==> m == m');

(*| States extensionality: maps that are `FStar.FiniteMap.Base.equal` are
    equal (`==`).

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `equal m1 m2`. *)
let map_extensionality_fact =
  forall (a: eqtype) (b: Type u#b) (m1: map a b) (m2: map a b).{:pattern equal m1 m2}
    equal m1 m2 ==> m1 == m2

/// We represent the following Dafny axiom with `disjoint_fact`:
///
/// axiom (forall<U, V> m: Map U V, m': Map U V ::
///  { Map#Disjoint(m, m') }
///    Map#Disjoint(m, m') <==> (forall o: U :: {Map#Domain(m)[o]} {Map#Domain(m')[o]} !Map#Domain(m)[o] || !Map#Domain(m')[o]));

(*| Characterizes `FStar.FiniteMap.Base.disjoint`: `disjoint m1 m2` holds
    exactly when no key is in both domains.

    Proved, not assumed, as part of
    `FStar.FiniteMap.Base.all_finite_map_facts`; the quantifier is triggered
    on `disjoint m1 m2`. *)
let disjoint_fact =
  forall (a: eqtype) (b: Type u#b) (m1: map a b) (m2: map a b).{:pattern disjoint m1 m2}
    disjoint m1 m2 <==> (forall key.{:pattern FSet.mem key (domain m1) \/ FSet.mem key (domain m2)}
                          not (FSet.mem key (domain m1)) || not (FSet.mem key (domain m2)))

(**
  The predicate `all_finite_map_facts` collects all the Dafny finite-map axioms.
  One can bring all these facts into scope with `all_finite_map_facts_lemma ()`.
**)

(*| The conjunction of all the `_fact` propositions of
    `FStar.FiniteMap.Base`: the F\* version of the finite-map axioms of the
    Dafny prelude, for value types in universe `b`.

    Each `_fact` is a universally quantified proposition with the SMT
    patterns of the corresponding Dafny axiom. They are not F\* axioms:
    `FStar.FiniteMap.Base.all_finite_map_facts_lemma` proves them from the
    implementation. Call that lemma to put them in the proof context, or
    open `FStar.FiniteMap.Ambient` to have them available whenever a map
    type occurs.

    Dafny axioms that would need the values or items to form finite sets,
    such as bounds on their cardinality, are omitted, since values need not
    have decidable equality. *)
let all_finite_map_facts =
    cardinality_zero_iff_empty_fact u#b
  /\ empty_or_domain_occupied_fact u#b
  /\ empty_or_values_occupied_fact u#b
  /\ empty_or_items_occupied_fact u#b
  /\ map_cardinality_matches_domain_fact u#b
  /\ values_contains_fact u#b
  /\ items_contains_fact u#b
  /\ empty_domain_empty_fact u#b
  /\ glue_domain_fact u#b
  /\ glue_elements_fact u#b
  /\ insert_elements_fact u#b
  /\ insert_member_cardinality_fact u#b
  /\ insert_nonmember_cardinality_fact u#b
  /\ merge_domain_is_union_fact u#b
  /\ merge_element_fact u#b
  /\ subtract_domain_fact u#b
  /\ subtract_element_fact u#b
  /\ map_equal_fact u#b
  /\ map_extensionality_fact u#b
  /\ disjoint_fact u#b
  
(*| Proves `FStar.FiniteMap.Base.all_finite_map_facts`; call it to bring
    every finite-map fact into the SMT context of the current proof.

    ```fstar
    let insert_then_read (m: FStar.FiniteMap.Base.map int string)
      : Lemma (FStar.FiniteMap.Base.elements (FStar.FiniteMap.Base.insert 1 "one" m) 1 == Some "one")
      = FStar.FiniteMap.Base.all_finite_map_facts_lemma ()
    ```

    The finite-set facts are separate; see
    `FStar.FiniteSet.Base.all_finite_set_facts_lemma`. *)
val all_finite_map_facts_lemma (_:unit)
  : Lemma (all_finite_map_facts u#b)
