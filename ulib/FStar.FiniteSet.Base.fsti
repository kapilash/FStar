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
finite sets as they're modeled in Dafny.

@summary Type and functions for modeling finite sets
*)
module FStar.FiniteSet.Base

open FStar.FunctionalExtensionality
module FLT = FStar.List.Tot

(*| The type of finite sets of elements of an `eqtype` `a`, modeled on
    Dafny's `Set T`.

    The type is abstract. Membership is `FStar.FiniteSet.Base.mem`, and set
    operations and their properties are stated by the `_fact` propositions
    of this module, collected in
    `FStar.FiniteSet.Base.all_finite_set_facts`. Equality of sets is not
    decidable; use `FStar.FiniteSet.Base.equal` and
    `FStar.FiniteSet.Base.equal_extensionality_fact` to prove two sets
    equal.

    This module is independent of `FStar.Set`, whose sets may be infinite. *)
val set (a: eqtype)
  : Type0

(**
  We translate each Dafny sequence function prefixed with `Set#`
  into an F* function.
**)

/// We represent the Dafny operator [] on sets with `mem`:

(*| Tests whether `x` is an element of the finite set `s` (Dafny's `s[x]` on
    sets).

    See also `FStar.FiniteSet.Base.notin`. *)
val mem (#a: eqtype) (x: a) (s: set a)
  : bool

/// We can convert a set to a list with `set_as_list`:

(*| Holds when no element occurs twice in the list `xs`.

    Used to specify `FStar.FiniteSet.Base.set_as_list`. *)
let rec list_nonrepeating (#a: eqtype) (xs: list a) : bool =
  match xs with
  | [] -> true
  | hd :: tl -> not (FLT.mem hd tl) && list_nonrepeating tl

(*| Returns, in ghost code, a list holding each element of `s` exactly once,
    in an unspecified order.

    `FStar.FiniteSet.Base.set_as_list_cardinality_fact` states that its
    length is `FStar.FiniteSet.Base.cardinality s`. *)
val set_as_list (#a: eqtype) (s: set a)
  : GTot (xs: list a{list_nonrepeating xs /\ (forall x. FLT.mem x xs = mem x s)})

/// We represent the Dafny function `Set#Card` with `cardinality`:
///
/// function Set#Card<T>(Set T): int;

(*| Returns, in ghost code, the number of elements of a finite set (Dafny's
    `Set#Card`).

    Its properties are given by the `_fact` propositions that mention it,
    such as `FStar.FiniteSet.Base.length_zero_fact`. *)
val cardinality (#a: eqtype) (s: set a)
  : GTot nat

/// We represent the Dafny function `Set#Empty` with `empty`:
///
/// function Set#Empty<T>(): Set T;

(*| The finite set with no elements (Dafny's `Set#Empty`).

    See `FStar.FiniteSet.Base.empty_set_contains_no_elements_fact`. *)
val emptyset (#a: eqtype)
  : set a

/// We represent the Dafny function `Set#UnionOne` with `insert`:
///
/// function Set#UnionOne<T>(Set T, T): Set T;

(*| Returns `s` with the element `x` added (Dafny's `Set#UnionOne`).

    Membership is given by `FStar.FiniteSet.Base.insert_fact`, cardinality
    by `FStar.FiniteSet.Base.insert_member_cardinality_fact` and
    `FStar.FiniteSet.Base.insert_nonmember_cardinality_fact`. *)
val insert (#a: eqtype) (x: a) (s: set a)
  : set a

/// We represent the Dafny function `Set#Singleton` with `singleton`:
///
/// function Set#Singleton<T>(T): Set T;

(*| Returns the finite set whose only element is `x` (Dafny's
    `Set#Singleton`). *)
val singleton (#a: eqtype) (x: a)
  : set a

/// We represent the Dafny function `Set#Union` with `union`:
///
/// function Set#Union<T>(Set T, Set T): Set T;

(*| Returns the set of elements in `s1` or in `s2` (Dafny's `Set#Union`).

    See `FStar.FiniteSet.Base.union_contains_fact`. *)
val union (#a: eqtype) (s1: set a) (s2: set a)
  : (set a)

/// We represent the Dafny function `Set#Intersection` with `intersection`:
///
/// function Set#Intersection<T>(Set T, Set T): Set T;

(*| Returns the set of elements in both `s1` and `s2` (Dafny's
    `Set#Intersection`).

    See `FStar.FiniteSet.Base.intersection_contains_fact`. *)
val intersection (#a: eqtype) (s1: set a) (s2: set a)
  : set a

/// We represent the Dafny function `Set#Difference` with `difference`:
///
/// function Set#Difference<T>(Set T, Set T): Set T;

(*| Returns the set of elements of `s1` that are not in `s2` (Dafny's
    `Set#Difference`).

    See `FStar.FiniteSet.Base.difference_contains_fact`. *)
val difference (#a: eqtype) (s1: set a) (s2: set a)
  : set a

/// We represent the Dafny function `Set#Subset` with `subset`:
///
/// function Set#Subset<T>(Set T, Set T): bool;

(*| Holds when every element of `s1` is an element of `s2` (Dafny's
    `Set#Subset`).

    The definition is abstract; `FStar.FiniteSet.Base.subset_fact`
    characterizes it. *)
val subset (#a: eqtype) (s1: set a) (s2: set a)
  : prop

/// We represent the Dafny function `Set#Equal` with `equal`:
///
/// function Set#Equal<T>(Set T, Set T): bool;

(*| Holds when `s1` and `s2` have the same elements (Dafny's `Set#Equal`).

    `FStar.FiniteSet.Base.equal_fact` characterizes it and
    `FStar.FiniteSet.Base.equal_extensionality_fact` turns it into
    `s1 == s2`. *)
val equal (#a: eqtype) (s1: set a) (s2: set a)
  : prop

/// We represent the Dafny function `Set#Disjoint` with `disjoint`:
///
/// function Set#Disjoint<T>(Set T, Set T): bool;

(*| Holds when `s1` and `s2` have no element in common (Dafny's
    `Set#Disjoint`).

    `FStar.FiniteSet.Base.disjoint_fact` characterizes it. *)
val disjoint (#a: eqtype) (s1: set a) (s2: set a)
  : prop

/// We represent the Dafny choice operator by `choose`:
///
/// var x: T :| x in s;

(*| Returns, in ghost code, some element of a nonempty finite set (Dafny's
    `x :| x in s`).

    The caller must prove that `s` has an element. Which element is returned
    is unspecified. *)
val choose (#a: eqtype) (s: set a{exists x. mem x s})
  : GTot (x: a{mem x s})

/// We add the utility functions `remove` and `notin`:

(*| Returns `s` without the element `x`; defined as
    `difference s (singleton x)`.

    See `FStar.FiniteSet.Base.insert_remove_fact` and
    `FStar.FiniteSet.Base.remove_insert_fact`. *)
let remove (#a: eqtype) (x: a) (s: set a)
  : set a =
  difference s (singleton x)

(*| Tests whether `x` is not an element of `s`; the negation of
    `FStar.FiniteSet.Base.mem`. *)
let notin (#a: eqtype) (x: a) (s: set a)
  : bool =
  not (mem x s)

(**
  We translate each finite set axiom from the Dafny prelude into an F*
  predicate ending in `_fact`.
**)

/// We don't need the following axiom since we return a nat from cardinality:
/// 
/// axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));

/// We represent the following Dafny axiom with `empty_set_contains_no_elements_fact`:
///
/// axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);

(*| States that `FStar.FiniteSet.Base.emptyset` has no elements.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `mem o emptyset`. *)
let empty_set_contains_no_elements_fact =
  forall (a: eqtype) (o: a).{:pattern mem o (emptyset)} not (mem o (emptyset #a))

/// We represent the following Dafny axiom with `length_zero_fact`:
///
/// axiom (forall<T> s: Set T :: { Set#Card(s) }
///  (Set#Card(s) == 0 <==> s == Set#Empty()) &&
///  (Set#Card(s) != 0 ==> (exists x: T :: s[x])));

(*| States that a set has cardinality 0 exactly when it is
    `FStar.FiniteSet.Base.emptyset`, and nonzero cardinality exactly when it
    has an element.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `cardinality s`. *)
let length_zero_fact =
  forall (a: eqtype) (s: set a).{:pattern cardinality s}
      (cardinality s = 0 <==> s == emptyset)
    /\ (cardinality s <> 0 <==> (exists x. mem x s))
    
/// We represent the following Dafny axiom with `singleton_contains_argument_fact`:
///
/// axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);

(*| States that `singleton r` contains `r`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `singleton r`. *)
let singleton_contains_argument_fact =
  forall (a: eqtype) (r: a).{:pattern singleton r} mem r (singleton r)
    
/// We represent the following Dafny axiom with `singleton_contains_fact`:
///
/// axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);

(*| States that `o` is in `singleton r` exactly when `r == o`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `mem o (singleton r)`. *)
let singleton_contains_fact =
  forall (a: eqtype) (r: a) (o: a).{:pattern mem o (singleton r)} mem o (singleton r) <==> r == o
    
/// We represent the following Dafny axiom with `singleton_cardinality_fact`:
///
/// axiom (forall<T> r: T :: { Set#Card(Set#Singleton(r)) } Set#Card(Set#Singleton(r)) == 1);

(*| States that a singleton set has cardinality 1.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `cardinality (singleton r)`. *)
let singleton_cardinality_fact =
  forall (a: eqtype) (r: a).{:pattern cardinality (singleton r)} cardinality (singleton r) = 1
    
/// We represent the following Dafny axiom with `insert_fact`:
///
/// axiom (forall<T> a: Set T, x: T, o: T :: { Set#UnionOne(a,x)[o] }
///  Set#UnionOne(a,x)[o] <==> o == x || a[o]);

(*| States that `o` is in `insert x s` exactly when `o == x` or `o` is in
    `s`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `mem o (insert x s)`. *)
let insert_fact =
  forall (a: eqtype) (s: set a) (x: a) (o: a).{:pattern mem o (insert x s)}
    mem o (insert x s) <==> o == x \/ mem o s
    
/// We represent the following Dafny axiom with `insert_contains_argument_fact`:
///
/// axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) }
///  Set#UnionOne(a, x)[x]);

(*| States that `insert x s` contains `x`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `insert x s`. *)
let insert_contains_argument_fact =
  forall (a: eqtype) (s: set a) (x: a).{:pattern insert x s}
    mem x (insert x s)
    
/// We represent the following Dafny axiom with `insert_contains_fact`:
///
/// axiom (forall<T> a: Set T, x: T, y: T :: { Set#UnionOne(a, x), a[y] }
///  a[y] ==> Set#UnionOne(a, x)[y]);

(*| States that every element of `s` is in `insert x s`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on both `insert x s` and `mem y s`. *)
let insert_contains_fact =
  forall (a: eqtype) (s: set a) (x: a) (y: a).{:pattern insert x s; mem y s}
    mem y s ==> mem y (insert x s)
    
/// We represent the following Dafny axiom with `insert_member_cardinality_fact`:
///
/// axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
///  a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));

(*| States that inserting an element already in `s` leaves the cardinality
    unchanged.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `cardinality (insert x s)`. *)
let insert_member_cardinality_fact =
  forall (a: eqtype) (s: set a) (x: a).{:pattern cardinality (insert x s)}
    mem x s ==> cardinality (insert x s) = cardinality s
    
/// We represent the following Dafny axiom with `insert_nonmember_cardinality_fact`:
///
/// axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
///  !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

(*| States that inserting an element not in `s` increases the cardinality by
    1.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `cardinality (insert x s)`. *)
let insert_nonmember_cardinality_fact =
  forall (a: eqtype) (s: set a) (x: a).{:pattern cardinality (insert x s)}
    not (mem x s) ==> cardinality (insert x s) = cardinality s + 1
    
/// We represent the following Dafny axiom with `union_contains_fact`:
///
/// axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Union(a,b)[o] }
///  Set#Union(a,b)[o] <==> a[o] || b[o]);

(*| States that `o` is in `union s1 s2` exactly when it is in `s1` or in
    `s2`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `mem o (union s1 s2)`. *)
let union_contains_fact =
  forall (a: eqtype) (s1: set a) (s2: set a) (o: a).{:pattern mem o (union s1 s2)}
    mem o (union s1 s2) <==> mem o s1 \/ mem o s2
    
/// We represent the following Dafny axiom with `union_contains_element_from_first_argument_fact`:
///
/// axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), a[y] }
///  a[y] ==> Set#Union(a, b)[y]);

(*| States that every element of `s1` is in `union s1 s2`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on both `union s1 s2` and `mem y s1`. *)
let union_contains_element_from_first_argument_fact =
  forall (a: eqtype) (s1: set a) (s2: set a) (y: a).{:pattern union s1 s2; mem y s1}
    mem y s1 ==> mem y (union s1 s2)
    
/// We represent the following Dafny axiom with `union_contains_element_from_second_argument_fact`:
///
/// axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), a[y] }
///  b[y] ==> Set#Union(a, b)[y]);

(*| States that every element of `s2` is in `union s1 s2`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on both `union s1 s2` and `mem y s2`. *)
let union_contains_element_from_second_argument_fact =
  forall (a: eqtype) (s1: set a) (s2: set a) (y: a).{:pattern union s1 s2; mem y s2}
    mem y s2 ==> mem y (union s1 s2)

/// We represent the following Dafny axiom with `union_of_disjoint_fact`:
///
/// axiom (forall<T> a, b: Set T :: { Set#Union(a, b) }
///  Set#Disjoint(a, b) ==>
///    Set#Difference(Set#Union(a, b), a) == b &&
///    Set#Difference(Set#Union(a, b), b) == a);

(*| States that for disjoint `s1` and `s2`, removing either set from their
    union gives back the other.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `union s1 s2`. *)
let union_of_disjoint_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern union s1 s2}
    disjoint s1 s2 ==> difference (union s1 s2) s1 == s2 /\ difference (union s1 s2) s2 == s1

/// We represent the following Dafny axiom with `intersection_contains_fact`:
///
/// axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Intersection(a,b)[o] }
///  Set#Intersection(a,b)[o] <==> a[o] && b[o]);

(*| States that `o` is in `intersection s1 s2` exactly when it is in both
    sets.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `mem o (intersection s1 s2)`. *)
let intersection_contains_fact =
  forall (a: eqtype) (s1: set a) (s2: set a) (o: a).{:pattern mem o (intersection s1 s2)}
    mem o (intersection s1 s2) <==> mem o s1 /\ mem o s2

/// We represent the following Dafny axiom with `union_idempotent_right_fact`:
///
/// axiom (forall<T> a, b: Set T :: { Set#Union(Set#Union(a, b), b) }
///  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));

(*| States that `union (union s1 s2) s2 == union s1 s2`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `union (union s1 s2) s2`. *)
let union_idempotent_right_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern union (union s1 s2) s2}
    union (union s1 s2) s2 == union s1 s2

/// We represent the following Dafny axiom with `union_idempotent_left_fact`:
///
/// axiom (forall<T> a, b: Set T :: { Set#Union(a, Set#Union(a, b)) }
///  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));

(*| States that `union s1 (union s1 s2) == union s1 s2`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `union s1 (union s1 s2)`. *)
let union_idempotent_left_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern union s1 (union s1 s2)}
    union s1 (union s1 s2) == union s1 s2

/// We represent the following Dafny axiom with `intersection_idempotent_right_fact`:
///
/// axiom (forall<T> a, b: Set T :: { Set#Intersection(Set#Intersection(a, b), b) }
///  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));

(*| States that
    `intersection (intersection s1 s2) s2 == intersection s1 s2`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `intersection (intersection s1 s2) s2`. *)
let intersection_idempotent_right_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern intersection (intersection s1 s2) s2}
    intersection (intersection s1 s2) s2 == intersection s1 s2

/// We represent the following Dafny axiom with `intersection_idempotent_left_fact`:
///
/// axiom (forall<T> a, b: Set T :: { Set#Intersection(a, Set#Intersection(a, b)) }
///  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));

(*| States that
    `intersection s1 (intersection s1 s2) == intersection s1 s2`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `intersection s1 (intersection s1 s2)`. *)
let intersection_idempotent_left_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern intersection s1 (intersection s1 s2)}
    intersection s1 (intersection s1 s2) == intersection s1 s2

/// We represent the following Dafny axiom with `intersection_cardinality_fact`:
///
/// axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }{ Set#Card(Set#Intersection(a, b)) }
///  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b)) == Set#Card(a) + Set#Card(b));

(*| States that the cardinalities of the union and the intersection of two
    sets add up to the sum of their cardinalities.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `cardinality (intersection s1 s2)` (unlike Dafny, not also on the
    cardinality of the union). *)
let intersection_cardinality_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern cardinality (intersection s1 s2)}
    cardinality (union s1 s2) + cardinality (intersection s1 s2) = cardinality s1 + cardinality s2

/// We represent the following Dafny axiom with `difference_contains_fact`:
///
/// axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Difference(a,b)[o] }
///  Set#Difference(a,b)[o] <==> a[o] && !b[o]);

(*| States that `o` is in `difference s1 s2` exactly when it is in `s1` and
    not in `s2`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `mem o (difference s1 s2)`. *)
let difference_contains_fact =
  forall (a: eqtype) (s1: set a) (s2: set a) (o: a).{:pattern mem o (difference s1 s2)}
    mem o (difference s1 s2) <==> mem o s1 /\ not (mem o s2)

/// We represent the following Dafny axiom with `difference_doesnt_include_fact`:
///
/// axiom (forall<T> a, b: Set T, y: T :: { Set#Difference(a, b), b[y] }
///  b[y] ==> !Set#Difference(a, b)[y] );

(*| States that no element of `s2` is in `difference s1 s2`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on both `difference s1 s2` and `mem y s2`. *)
let difference_doesnt_include_fact =
  forall (a: eqtype) (s1: set a) (s2: set a) (y: a).{:pattern difference s1 s2; mem y s2}
    mem y s2 ==> not (mem y (difference s1 s2))

/// We represent the following Dafny axiom with `difference_cardinality_fact`:
///
/// axiom (forall<T> a, b: Set T ::
///  { Set#Card(Set#Difference(a, b)) }
///  Set#Card(Set#Difference(a, b)) + Set#Card(Set#Difference(b, a))
///  + Set#Card(Set#Intersection(a, b))
///    == Set#Card(Set#Union(a, b)) &&
///  Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

(*| Relates the cardinality of a set difference to the cardinalities of the
    union and intersection.

    It states that the cardinalities of `difference s1 s2`,
    `difference s2 s1` and `intersection s1 s2` add up to that of
    `union s1 s2`, and that the cardinality of `difference s1 s2` is that of
    `s1` minus that of `intersection s1 s2`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `cardinality (difference s1 s2)`. *)
let difference_cardinality_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern cardinality (difference s1 s2)}
      cardinality (difference s1 s2) + cardinality (difference s2 s1) + cardinality (intersection s1 s2) = cardinality (union s1 s2)
    /\ cardinality (difference s1 s2) = cardinality s1 - cardinality (intersection s1 s2)

/// We represent the following Dafny axiom with `subset_fact`:
///
/// axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b) }
///  Set#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));

(*| Characterizes `FStar.FiniteSet.Base.subset`: `subset s1 s2` holds
    exactly when every element of `s1` is in `s2`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `subset s1 s2`. *)
let subset_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern subset s1 s2}
    subset s1 s2 <==> (forall o.{:pattern mem o s1 \/ mem o s2} mem o s1 ==> mem o s2)

/// We represent the following Dafny axiom with `equal_fact`:
///
/// axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }
///  Set#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));

(*| Characterizes `FStar.FiniteSet.Base.equal`: `equal s1 s2` holds exactly
    when the sets have the same elements.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `equal s1 s2`. *)
let equal_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern equal s1 s2}
    equal s1 s2 <==> (forall o.{:pattern mem o s1 \/ mem o s2} mem o s1 <==> mem o s2)

/// We represent the following Dafny axiom with `equal_extensionality_fact`:
///
/// axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }  // extensionality axiom for sets
///  Set#Equal(a,b) ==> a == b);

(*| States extensionality: sets that are `FStar.FiniteSet.Base.equal` are
    equal (`==`).

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `equal s1 s2`. *)
let equal_extensionality_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern equal s1 s2}
    equal s1 s2 ==> s1 == s2

/// We represent the following Dafny axiom with `disjoint_fact`:
///
/// axiom (forall<T> a: Set T, b: Set T :: { Set#Disjoint(a,b) }
///  Set#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));

(*| Characterizes `FStar.FiniteSet.Base.disjoint`: `disjoint s1 s2` holds
    exactly when no element is in both sets.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `disjoint s1 s2`. *)
let disjoint_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern disjoint s1 s2}
    disjoint s1 s2 <==> (forall o.{:pattern mem o s1 \/ mem o s2} not (mem o s1) \/ not (mem o s2))

/// We add a few more facts for the utility function `remove` and for `set_as_list`:

(*| States that removing then reinserting an element of `s` gives back `s`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `insert x (remove x s)`. *)
let insert_remove_fact =
  forall (a: eqtype) (x: a) (s: set a).{:pattern insert x (remove x s)}
    mem x s = true ==> insert x (remove x s) == s

(*| States that inserting then removing an element not in `s` gives back
    `s`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `remove x (insert x s)`. *)
let remove_insert_fact =
  forall (a: eqtype) (x: a) (s: set a).{:pattern remove x (insert x s)}
    mem x s = false ==> remove x (insert x s) == s

(*| States that the length of `set_as_list s` is the cardinality of `s`.

    Proved, not assumed, as part of
    `FStar.FiniteSet.Base.all_finite_set_facts`; the quantifier is triggered
    on `FStar.List.Tot.length (set_as_list s)`. *)
let set_as_list_cardinality_fact =
  forall (a: eqtype) (s: set a).{:pattern FLT.length (set_as_list s)}
    FLT.length (set_as_list s) = cardinality s

(**
  The predicate `all_finite_set_facts` collects all the Dafny finite-set axioms.
  One can bring all these facts into scope with `all_finite_set_facts_lemma ()`.
**)

(*| The conjunction of all the `_fact` propositions of
    `FStar.FiniteSet.Base`: the F\* version of the finite-set axioms of the
    Dafny prelude, plus facts about `remove` and `set_as_list`.

    Each `_fact` is a universally quantified proposition with the SMT
    patterns of the corresponding Dafny axiom. They are not F\* axioms:
    `FStar.FiniteSet.Base.all_finite_set_facts_lemma` proves them from the
    implementation. Call that lemma to put them in the proof context, or
    open `FStar.FiniteSet.Ambient` to have them available everywhere. *)
let all_finite_set_facts =
    empty_set_contains_no_elements_fact
  /\ length_zero_fact
  /\ singleton_contains_argument_fact
  /\ singleton_contains_fact
  /\ singleton_cardinality_fact
  /\ insert_fact
  /\ insert_contains_argument_fact
  /\ insert_contains_fact
  /\ insert_member_cardinality_fact
  /\ insert_nonmember_cardinality_fact
  /\ union_contains_fact
  /\ union_contains_element_from_first_argument_fact
  /\ union_contains_element_from_second_argument_fact
  /\ union_of_disjoint_fact
  /\ intersection_contains_fact
  /\ union_idempotent_right_fact
  /\ union_idempotent_left_fact
  /\ intersection_idempotent_right_fact
  /\ intersection_idempotent_left_fact
  /\ intersection_cardinality_fact
  /\ difference_contains_fact
  /\ difference_doesnt_include_fact
  /\ difference_cardinality_fact
  /\ subset_fact
  /\ equal_fact
  /\ equal_extensionality_fact
  /\ disjoint_fact
  /\ insert_remove_fact
  /\ remove_insert_fact
  /\ set_as_list_cardinality_fact

(*| Proves `FStar.FiniteSet.Base.all_finite_set_facts`; call it to bring
    every finite-set fact into the SMT context of the current proof.

    ```fstar
    let two_elements ()
      : Lemma (FStar.FiniteSet.Base.cardinality
                 (FStar.FiniteSet.Base.insert 1 (FStar.FiniteSet.Base.singleton 2)) = 2)
      = FStar.FiniteSet.Base.all_finite_set_facts_lemma ()
    ```

    To have the facts in every proof of a module, depend on
    `FStar.FiniteSet.Ambient` instead. *)
val all_finite_set_facts_lemma : unit -> Lemma (all_finite_set_facts)
