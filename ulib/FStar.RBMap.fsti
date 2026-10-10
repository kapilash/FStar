(*
   Copyright 2008-2025 Microsoft Research

   Authors: Guido Martínez

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

module FStar.RBMap

open FStar.Class.Ord.Raw

(*| Abstract type of finite maps from keys of type `a` to values of type `b`, implemented as red-black trees.

    Keys are compared with an `FStar.Class.Ord.Raw.ord` instance, which most
    operations take as a typeclass argument; two keys are the same when the
    comparison says they are equal. All operations are total, but the interface
    states no functional specification, so the behaviour described in these
    docs is that of the implementation and cannot be used in proofs. The
    module is mostly useful for unverified code. Use `FStar.RBMap.equal` to
    compare maps.

    ```fstar
    let ages : FStar.RBMap.t string int = FStar.RBMap.from_list [("alice", 30); ("bob", 25)]
    let bob_age : option int = FStar.RBMap.lookup "bob" ages
    ``` *)
new val t (a b :Type0) : Type0

(*| The map with no bindings. *)
val empty () : t 'a 'b

(*| The map with a single binding of key `x` to value `y`. *)
val singleton (x :'a) (y : 'b) : t 'a 'b

(*| Tests whether a map has no bindings. *)
val is_empty (s : t 'a 'b) : bool

(*| Adds a binding of key `x` to value `vx`, unless `x` is already bound.

    Caution: if `x` is already present, the map is returned unchanged and the
    existing value is kept; `add` does not overwrite. To replace a value,
    `FStar.RBMap.remove` the key first. *)
val add {| ord 'a |} (x:'a) (vx : 'b) (s:t 'a 'b) : t 'a 'b

(*| Keeps only the bindings `(k, v)` for which `predicate k v` is `true`. *)
val filter {| ord 'a |} (predicate: 'a -> 'b -> bool) (set: t 'a 'b) : t 'a 'b

(*| Removes the binding with the smallest key from a nonempty map, returning the remaining map and that binding.

    Requires `not (is_empty m)`. The result is the pair of the remaining map
    and the `(key, value)` binding, in that order. *)
val extract_min #a #b {| ord a |} (m : t a b{not (is_empty m)}) : t a b & (a & b)

(*| Removes the binding of key `x`, if any; returns the map unchanged if `x` is not bound. *)
val remove {| ord 'a |} (x : 'a) (m : t 'a 'b) : t 'a 'b

(*| Tests whether key `x` is bound in the map. *)
val mem {| ord 'a |} (x : 'a) (m : t 'a 'b) : bool

(*| Returns `Some` of the value bound to key `x`, or `None` if `x` is not bound. *)
val lookup {| ord 'a |} (x : 'a) (m : t 'a 'b) : option 'b

(*| The keys of a map, in increasing order. *)
val keys (s : t 'a 'b) : list 'a

(*| The bindings of a map as `(key, value)` pairs, in increasing key order. *)
val to_list (s : t 'a 'b) : list ('a & 'b)

(*| Tests whether two maps have the same bindings.

    Compares `FStar.RBMap.to_list s1` and `FStar.RBMap.to_list s2` with
    decidable equality: keys with the equality of the `ord` instance and values
    with the `FStar.Class.Eq.Raw.deq` instance for `b`. *)
val equal {| ord 'a, Class.Eq.Raw.deq 'b |} (s1 s2 : t 'a 'b) : bool

(*| The union of two maps; when a key is bound in both, the value from the second map `s2` is kept.

    This follows from `FStar.RBMap.add` not overwriting existing bindings: the
    bindings of `s1` are added into `s2`. *)
val union {| ord 'a |} (s1 s2 : t 'a 'b) : t 'a 'b

(*| The intersection of two maps: keys bound in both, with values from the first map `s1`.

    It is left-biased: values from `s2` are never used. *)
val inter {| ord 'a |} (s1 s2 : t 'a 'b) : t 'a 'b

(*| Tests whether every binding `(k, v)` satisfies `p k v`; `true` for the empty map. *)
val for_all (p : 'a -> 'b -> bool) (s : t 'a 'b) : bool

(*| Intended to test whether some binding `(k, v)` satisfies `p k v`.

    Caution: the current implementation returns `true` if the binding at the
    root of the tree satisfies `p`, and otherwise only if every binding of
    both subtrees satisfies `p` (it uses `FStar.RBMap.for_all` on the
    subtrees). It can therefore return `false` even though some binding
    satisfies `p`; its result depends on the tree shape. It returns `false`
    for the empty map. *)
val for_any (p : 'a -> 'b -> bool) (s : t 'a 'b) : bool

(*| Builds a map from a list of `(key, value)` pairs.

    The pairs are added from left to right with `FStar.RBMap.add`, so when a
    key occurs several times its first occurrence wins. *)
val from_list {| ord 'a |} (xs : list ('a & 'b)) : t 'a 'b

(*| Adds a list of `(key, value)` pairs to a map, from left to right with `FStar.RBMap.add`.

    Keys already bound in `s` keep their value, and among repeated keys of the
    list the first occurrence wins. *)
val addn {| ord 'a |} (xs : list ('a & 'b)) (s : t 'a 'b) : t 'a 'b
