(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Aseem Rastogi and Nikhil Swamy
*)

module FStar.LexicographicOrdering

/// This module proves that lexicographic ordering is well-founded
///   (i.e. every element is accessible)
///
/// It defines the lex relation as an inductive, and prove its well-foundedness
///
/// Since SMT proofs in F* are more amenable to squashed definitions,
///   the module also defines a squashed version of the lex relation,
///   and prove its well-foundedness, reusing the proof for the constructive version
///
/// See tests/micro-benchmarks/Test.WellFoundedRecursion.fst for
///   how we use squashed `lex` to prove termination for the ackermann function
///
/// Finally, the module defines a non-dependent version of lex
///   (in-terms of dependent lex), and uses it to prove well-foundedness of symmetric products too
/// 
/// Some references:
///   - https://github.com/coq/coq/blob/master/theories/Wellfounded/Lexicographic_Product.v
///   - Constructing Recursion Operators in Type Theory, L. Paulson  JSC (1986) 2, 325-355

open FStar.WellFounded


/// Definition of lexicographic ordering as a relation over dependent tuples
///
/// Two elements are related if:
///   - Either their first components are related
///   - Or, the first components are equal, and the second components are related

(*| The lexicographic order on dependent pairs: `(| x1, y1 |)` precedes
    `(| x2, y2 |)` when `r_a x1 x2`, or `x1 == x2` and `r_b x1 y1 y2`.

    The relation is squashed (a `prop`), which suits SMT proofs. It is
    well-founded when `r_a` and every `r_b x` are, see
    `FStar.LexicographicOrdering.lex_t_wf`. *)
let lex_t (#a:Type u#a) (#b:a -> Type u#b)
  (r_a:binrel u#a a)
  (r_b:(x:a -> binrel u#b (b x)))
  : binrel u#(max a b) (x:a & b x)
  = fun (| x1, y1 |) (| x2, y2 |) ->
    r_a x1 x2 \/
    (x1 == x2 /\ r_b x1 y1 y2)

/// Given two well-founded relations `r_a` and `r_b`,
///   their lexicographic ordering is also well-founded

(*| The lexicographic order `FStar.LexicographicOrdering.lex_t r_a r_b` is
    well-founded when `r_a` and each `r_b x` are. *)
val lex_t_wf (#a:Type u#a) (#b:a -> Type u#b)
  (#r_a:binrel u#a a)
  (#r_b:(x:a -> binrel u#b (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : well_founded (lex_t r_a r_b)

/// And prove that is it is well-founded

(*| Propositional form of `FStar.LexicographicOrdering.lex_t_wf`: the
    lexicographic order is `FStar.WellFounded.is_well_founded`. *)
let lex_wf (#a:Type u#a) (#b:a -> Type u#b)
  (#r_a:binrel u#a a)
  (#r_b:(x:a -> binrel u#b (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : Lemma (is_well_founded (lex_t r_a r_b))
  = is_well_founded_of_well_founded (lex_t_wf wf_a wf_b)


/// A user-friendly lex_wf that returns a well-founded relation

(*| The lexicographic order on dependent pairs as a
    `FStar.WellFounded.well_founded_relation`, given well-foundedness proofs
    for both components.

    Useful in `decreases` clauses, for instance to prove termination of the
    Ackermann function. *)
unfold
let lex (#a:Type u#a) (#b:a -> Type u#b)
  (#r_a:binrel u#a a)
  (#r_b:(x:a -> binrel u#b (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : well_founded_relation (x:a & b x)
  = lex_wf wf_a wf_b;
    lex_t r_a r_b


/// We can also define a non-dependent version of the lex ordering,
///   in terms of the dependent lex tuple,
///   and prove its well-foundedness

(*| Converts a non-dependent pair `(x, y)` to the dependent pair `(| x, y |)`. *)
let tuple_to_dep_tuple (#a #b:Type) (x:a & b) : dtuple2 a (fun _ -> b) =
  (| fst x, snd x |)


/// The non-dependent lexicographic ordering
///   and its well-foundedness

(*| The lexicographic order on non-dependent pairs: `(x1, y1)` precedes
    `(x2, y2)` when `r_a x1 x2`, or `x1 == x2` and `r_b y1 y2`.

    Defined via `FStar.LexicographicOrdering.lex_t` and
    `FStar.LexicographicOrdering.tuple_to_dep_tuple`. *)
let lex_t_non_dep (#a:Type u#a) 
                  (#b:Type u#b)
                  (r_a:binrel u#a a)
                  (r_b:binrel u#b b)
  : binrel u#(max a b) (a & b)
  = fun x y ->
      lex_t r_a (fun _ -> r_b) (tuple_to_dep_tuple x) (tuple_to_dep_tuple y)

(*| The non-dependent lexicographic order
    `FStar.LexicographicOrdering.lex_t_non_dep r_a r_b` is well-founded when
    `r_a` and `r_b` are. *)
val lex_t_non_dep_wf (#a:Type u#a)
                     (#b:Type u#b)
                     (#r_a:binrel u#a a)
                     (#r_b:binrel u#b b)
                     (wf_a:well_founded r_a)
                     (wf_b:well_founded r_b)
  : well_founded (lex_t_non_dep r_a r_b)


/// Symmetric product relation
///   we can prove its well-foundedness by showing that it is a subrelation of non-dep lex

(*| The symmetric product of two relations: two pairs are related when one
    component is equal and the other component is related by its relation. *)
let sym (#a:Type u#a) (#b:Type u#b) (r_a:binrel u#a a) (r_b:binrel u#b b)
    (x: a & b) (y : a & b) : prop =
  (snd x == snd y /\ r_a (fst x) (fst y)) \/
  (fst x == fst y /\ r_b (snd x) (snd y))

/// sym is a subrelation of non-dependent lex

(*| The symmetric product `FStar.LexicographicOrdering.sym r_a r_b` is a
    subrelation of the lexicographic order
    `FStar.LexicographicOrdering.lex_t_non_dep r_a r_b`. *)
let sym_sub_lex (#a:Type u#a)
                (#b:Type u#b)
                (#r_a:binrel u#a a)
                (#r_b:binrel u#b b)
                (t1 t2:a & b)
                (p:sym r_a r_b t1 t2)
  : lex_t_non_dep r_a r_b t1 t2
  = ()

/// Theorem for symmetric product
///
(*| The symmetric product `FStar.LexicographicOrdering.sym r_a r_b` is
    well-founded when `r_a` and `r_b` are.

    Proved from `FStar.LexicographicOrdering.sym_sub_lex` and
    `FStar.WellFounded.subrelation_wf`. *)
let sym_wf (#a:Type u#a)
           (#b:Type u#b)
           (#r_a:binrel u#a a)
           (#r_b:binrel u#b b)
           (wf_a:well_founded r_a)
           (wf_b:well_founded r_b)
  : well_founded (sym r_a r_b)
  = subrelation_wf sym_sub_lex (lex_t_non_dep_wf wf_a wf_b)
