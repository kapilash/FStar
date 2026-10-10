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
module FStar.Reflection.V2.Compare

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Order

(*| Compares two qualified names lexicographically, component by component,
    with string comparison on each component. *)
[@@plugin]
val compare_name (n1 n2 : name) : order

(*| Compares two top-level names by their qualified names, with
    `FStar.Reflection.V2.Compare.compare_name`. *)
[@@plugin]
val compare_fv (f1 f2 : fv) : order

(*| Compares two reflected constants.

    Constants of the same kind compare by value (integers numerically, strings
    and characters by code, machine integers by value, then signedness, then
    width; reals with `FStar.RealLiteral.compare`); range constants are all
    equal. Constants of different kinds are ordered by constructor in the
    order of `FStar.Stubs.Reflection.V2.Data.vconst`. *)
[@@plugin]
val compare_const (c1 c2 : vconst) : order

(*| Compares two identifiers by their names, ignoring their ranges. *)
[@@plugin]
val compare_ident (i1 i2:ident) : order

(*| Compares two universes structurally.

    Universe unification variables all compare as equal, and named universe
    variables compare by name with `FStar.Reflection.V2.Compare.compare_ident`. *)
[@@plugin]
val compare_universe (u1 u2:universe) : order

(*| Compares two lists of universes lexicographically with
    `FStar.Reflection.V2.Compare.compare_universe`. *)
[@@plugin]
val compare_universes (us1 us2:universes) : order

(*| Compares two terms structurally, giving an ordering for sorting and
    canonicalization.

    Terms with different top-level constructors are ordered by constructor.
    Applications compare their heads first, then their argument lists, so
    `f a b` and `g a b` are ordered by `f` and `g`. Variables compare by unique
    number or de Bruijn index, top-level names by name.

    The comparison is coarse: it ignores binder names, qualifiers and
    attributes (binders compare by sort only), the attributes and recursion
    flag of `let`, the flags of computation types, and ranges. All `match`
    terms compare as `Eq`, as do all `Tv_Unknown` and all `Tv_Unsupp`. So `Eq`
    does not imply that the terms are equal; use
    `FStar.Reflection.TermEq.Simple.term_eq` to decide equality. *)
[@@plugin]
val compare_term (s t : term) : order

(*| Compares two computation types by effect name and then by result type with
    `FStar.Reflection.V2.Compare.compare_term`.

    The source effect name and the flags (SMT patterns and decreases clauses)
    are ignored. *)
[@@plugin]
val compare_comp (c1 c2 : comp) : order

(*| Compares two binders by their sorts only, with
    `FStar.Reflection.V2.Compare.compare_term`.

    Names, qualifiers and attributes are ignored. *)
[@@plugin]
val compare_binder (b1 b2 : binder) : order
