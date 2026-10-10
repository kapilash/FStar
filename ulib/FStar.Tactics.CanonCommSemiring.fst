(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.Tactics.CanonCommSemiring

/// A tactic to solve equalities on a commutative semiring (a, +, *, 0, 1)
///
/// The tactic [canon_semiring] is parameterized by the base type [a] and
/// a semiring theory [cr a]. This requires:
///
/// - A commutative monoid (a, +, 0) for addition
///   That is, + is associative, commutative and has identity element 0
/// - An additive inverse operator for (a, +, 0), making it an Abelian group
///   That is, a + -a = 0
/// - A commutative monoid (a, *, 1) for multiplication
///   That is, * is associative, commutative and has identity element 1
/// - Multiplication left-distributes over addition
///   That is, a * (b + c) == a * b + a * c
/// - 0 is an absorbing element of multiplication
///   That is, 0 * a = 0
///
/// In contrast to the previous version of FStar.Tactics.CanonCommSemiring,
/// the tactic defined here canonizes products, additions and additive inverses,
/// collects coefficients in monomials, and eliminates trivial expressions.
///
/// This is based on the legacy (second) version of Coq's ring tactic:
///  -  https://github.com/coq-contribs/legacy-ring/
///
/// See also the newest ring tactic in Coq, which is even more general
/// and efficient:
///  - https://coq.inria.fr/refman/addendum/ring.html
///  - http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf

open FStar.List
open FStar.Algebra.CommMonoid

(* Trying to not just open FStar.Tactics.V2 to reduce deps.
TODO: Add an interface to this module. It's non trivial due to the quoting. *)
open FStar.Stubs.Reflection.Types
open FStar.Reflection.V2
open FStar.Reflection.V2.Formula
open FStar.Stubs.Tactics.Types
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Tactics.V2.Derived
open FStar.Tactics.Util
open FStar.Tactics.NamedView
open FStar.Tactics.MApply

private
let term_eq = FStar.Reflection.TermEq.Simple.term_eq

(*| Attribute marking the definitions that the semiring tactic unfolds when normalizing its goals.

    `FStar.Tactics.CanonCommSemiring.steps` unfolds every definition carrying it with `delta_attr`. Attach it to a custom `FStar.Tactics.CanonCommSemiring.cr` instance and its auxiliary definitions so that they are unfolded too. *)
irreducible let canon_attr = ()

///
/// Commutative semiring theory
///

(*| The statement that multiplication `cm_mult` distributes over addition `cm_add` on the left: `x * (y + z) == x * y + x * z` for all `x`, `y` and `z`. *)
let distribute_left_lemma (a:Type) (cm_add:cm a) (cm_mult:cm a) =
  let ( + ) = cm_add.mult in
  let ( * ) = cm_mult.mult in
  x:a -> y:a -> z:a -> Lemma (x * (y + z) == x * y + x * z)

(*| The statement that multiplication `cm_mult` distributes over addition `cm_add` on the right: `(x + y) * z == x * z + y * z` for all `x`, `y` and `z`. *)
let distribute_right_lemma (a:Type) (cm_add:cm a) (cm_mult:cm a) =
  let ( + ) = cm_add.mult in
  let ( * ) = cm_mult.mult in
  x:a -> y:a -> z:a -> Lemma ((x + y) * z == x * z + y * z)

(*| The statement that the additive unit is a left zero of multiplication: `0 * x == 0` for all `x`, where `0` is the unit of `cm_add`. *)
let mult_zero_l_lemma (a:Type) (cm_add:cm a) (cm_mult:cm a) =
  x:a -> Lemma (cm_mult.mult cm_add.unit x == cm_add.unit)

(*| The statement that `opp` gives additive inverses: `x + opp x == 0` for all `x`, where `0` is the unit of `cm_add`. *)
let add_opp_r_lemma (a:Type) (cm_add:cm a) (opp:(a -> a)) =
  let ( + ) = cm_add.mult in
  x:a -> Lemma (x + opp x == cm_add.unit)

(*| Commutative ring structures on a type `a`, the theory used by `FStar.Tactics.CanonCommSemiring.canon_semiring`.

    The single constructor `CR` takes the additive commutative monoid `cm_add` (with unit `0`), the multiplicative commutative monoid `cm_mult` (with unit `1`), an additive inverse `opp` with proof `add_opp` of `FStar.Tactics.CanonCommSemiring.add_opp_r_lemma`, a proof `distribute` of left distributivity (`FStar.Tactics.CanonCommSemiring.distribute_left_lemma`) and a proof `mult_zero_l` that `0` is a left zero of multiplication (`FStar.Tactics.CanonCommSemiring.mult_zero_l_lemma`). Right distributivity follows, see `FStar.Tactics.CanonCommSemiring.distribute_right`. The integer instance is `FStar.Tactics.CanonCommSemiring.int_cr`. *)
[@@canon_attr]
unopteq
type cr (a:Type) =
  | CR :
    cm_add: cm a ->
    cm_mult: cm a ->
    opp: (a -> a) ->
    add_opp: add_opp_r_lemma a cm_add opp ->
    distribute: distribute_left_lemma a cm_add cm_mult ->
    mult_zero_l: mult_zero_l_lemma a cm_add cm_mult ->
    cr a

(*| Derives right distributivity, `FStar.Tactics.CanonCommSemiring.distribute_right_lemma`, for a commutative ring from left distributivity and commutativity of multiplication. *)
let distribute_right (#a:Type) (r:cr a) : distribute_right_lemma a r.cm_add r.cm_mult =
  fun x y z ->
    r.cm_mult.commutativity (r.cm_add.mult x y) z;
    r.distribute z x y;
    r.cm_mult.commutativity x z;
    r.cm_mult.commutativity y z

///
/// Syntax of canonical ring expressions
///

(*| Identity function marking ring expressions, such as sums of coefficients, that should be fully normalized.

    The marker has no effect at the moment beyond being unfolded by `FStar.Tactics.CanonCommSemiring.steps`; it records where a cheaper targeted normalization could apply. *)
[@@canon_attr]
unfold let norm_fully (#a:Type) (x:a) = x

(*| Indices of the variables of a reflected polynomial: natural numbers, looked up in a `FStar.Tactics.CanonCommSemiring.vmap`. *)
let index: eqtype = nat

(*| Products of variables, the monomials without coefficient of a canonical sum.

    `Nil_var` is the empty product, interpreted as `1`, and `Cons_var i l` is the product of the variable `i` and `l`. The variables are kept sorted by index by the operations of this module, although sortedness is never stated or needed for correctness. *)
type varlist =
  | Nil_var : varlist
  | Cons_var : index -> varlist -> varlist

(*| Canonical forms of polynomials: sums of monomials ordered by `FStar.Tactics.CanonCommSemiring.varlist_lt` on their variable lists.

    `Nil_monom` is the empty sum (`0`). `Cons_monom c l s` adds the monomial `c * l` with coefficient `c` to `s`, and `Cons_varlist l s` adds the monomial `l` with implicit coefficient `1`. `FStar.Tactics.CanonCommSemiring.interp_cs` gives their meaning. *)
type canonical_sum a =
  | Nil_monom : canonical_sum a
  | Cons_monom : a -> varlist -> canonical_sum a -> canonical_sum a
  | Cons_varlist : varlist -> canonical_sum a -> canonical_sum a

(*| Strict order on variable lists: lexicographic on the indices, with a shorter list smaller than any list it is a proper prefix of.

    Used to order the monomials of a `FStar.Tactics.CanonCommSemiring.canonical_sum`. *)
[@@canon_attr]
let rec varlist_lt (x y:varlist) : bool =
  match x, y with
  | Nil_var, Cons_var _ _ -> true
  | Cons_var i xs, Cons_var j ys ->
    if i < j then true else i = j && varlist_lt xs ys
  | _, _ -> false

(*| Multiplies two variable lists by merging them, keeping the variables sorted by index when both inputs are sorted.

    Its correctness is `FStar.Tactics.CanonCommSemiring.varlist_merge_ok`. *)
[@@canon_attr]
val varlist_merge: l1:varlist -> l2:varlist -> Tot varlist (decreases %[l1; l2; 0])

(*| Auxiliary function of `FStar.Tactics.CanonCommSemiring.varlist_merge`: merges the variable list `Cons_var v t` with `l`.

    Its correctness is `FStar.Tactics.CanonCommSemiring.vm_aux_ok`. *)
[@@canon_attr]
val vm_aux: index -> t1:varlist -> l2:varlist -> Tot varlist (decreases %[t1; l2; 1])

(* Merges two lists of variables, preserving sortedness *)
[@@canon_attr]
let rec varlist_merge l1 l2 =
  match l1, l2 with
  | _, Nil_var -> l1
  | Nil_var, _ -> l2
  | Cons_var v1 t1, Cons_var v2 t2 -> vm_aux v1 t1 l2
and vm_aux v1 t1 l2 =
  match l2 with
  | Cons_var v2 t2 ->
    if v1 < v2
    then Cons_var v1 (varlist_merge t1 l2)
    else Cons_var v2 (vm_aux v1 t1 t2)
  | _ -> Cons_var v1 t1

(*
 * Merges two canonical expressions
 *
 * We require that [a] is eqtype for better reasons later.
 * Here it is convenient to fix the universe of [a] in
 * mutually recursive functions.
 *)
(*| Adds two canonical sums by merging their monomials in `FStar.Tactics.CanonCommSemiring.varlist_lt` order, adding the coefficients of monomials with the same variable list.

    Monomials of the first sum without coefficient get the coefficient `1`, so the result may contain `1 * l`, which `FStar.Tactics.CanonCommSemiring.canonical_sum_simplify` removes. The carrier is required to be an `eqtype`. Its correctness is `FStar.Tactics.CanonCommSemiring.canonical_sum_merge_ok`. *)
[@@canon_attr]
val canonical_sum_merge : #a:eqtype -> cr a
  -> s1:canonical_sum a -> s2:canonical_sum a
  -> Tot (canonical_sum a) (decreases %[s1; s2; 0])

(*| Auxiliary function of `FStar.Tactics.CanonCommSemiring.canonical_sum_merge`: adds the canonical sum `Cons_monom c1 l1 t1` and `s2`.

    Its correctness is `FStar.Tactics.CanonCommSemiring.csm_aux_ok`. *)
[@@canon_attr]
val csm_aux: #a:eqtype -> r:cr a -> c1:a -> l1:varlist -> t1:canonical_sum a
  -> s2:canonical_sum a -> Tot (canonical_sum a) (decreases %[t1; s2; 1])

[@@canon_attr]
let rec canonical_sum_merge #a r s1 s2 =
  let aplus = r.cm_add.mult in
  let aone  = r.cm_mult.unit in
  match s1 with
  | Cons_monom c1 l1 t1 -> csm_aux r c1 l1 t1 s2
  | Cons_varlist l1 t1  -> csm_aux r aone l1 t1 s2
  | Nil_monom -> s2

and csm_aux #a r c1 l1 t1 s2 =
  let aplus = r.cm_add.mult in
  let aone  = r.cm_mult.unit in
  match s2 with
  | Cons_monom c2 l2 t2 ->
    if l1 = l2
    then Cons_monom (norm_fully (aplus c1 c2)) l1 (canonical_sum_merge r t1 t2)
    else
      if varlist_lt l1 l2
      then Cons_monom c1 l1 (canonical_sum_merge r t1 s2)
      else Cons_monom c2 l2 (csm_aux #a r c1 l1 t1 t2)
  | Cons_varlist l2 t2 ->
    if l1 = l2
    then Cons_monom (norm_fully (aplus c1 aone)) l1 (canonical_sum_merge r t1 t2)
    else
      if varlist_lt l1 l2
      then Cons_monom c1 l1 (canonical_sum_merge r t1 s2)
      else Cons_varlist l2 (csm_aux r c1 l1 t1 t2)
  | Nil_monom ->
    //if c1 = aone then Cons_varlist l1 t1 else
    Cons_monom c1 l1 t1

(*| Adds the monomial `c1 * l1` to a canonical sum at its ordered position, adding `c1` to the coefficient of a monomial with the same variable list if there is one.

    When inserted into an empty sum with `c1` equal to `1`, the monomial is stored without coefficient. Its correctness is `FStar.Tactics.CanonCommSemiring.monom_insert_ok`. *)
val monom_insert: #a:eqtype -> r:cr a
  -> c1:a -> l1:varlist -> s2:canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec monom_insert #a r c1 l1 s2 =
  let aplus = r.cm_add.mult in
  let aone  = r.cm_mult.unit in
  match s2 with
  | Cons_monom c2 l2 t2 ->
    if l1 = l2
    then Cons_monom (norm_fully (aplus c1 c2)) l1 t2
    else
      if varlist_lt l1 l2
      then Cons_monom c1 l1 s2
      else Cons_monom c2 l2 (monom_insert r c1 l1 t2)
  | Cons_varlist l2 t2 ->
    if l1 = l2
    then Cons_monom (norm_fully (aplus c1 aone)) l1 t2
    else
      if varlist_lt l1 l2
      then Cons_monom c1 l1 s2
      else Cons_varlist l2 (monom_insert r c1 l1 t2)
  | Nil_monom ->
    if c1 = aone
    then Cons_varlist l1 Nil_monom
    else Cons_monom c1 l1 Nil_monom

(*| Adds the monomial `l1`, with coefficient `1`, to a canonical sum using `FStar.Tactics.CanonCommSemiring.monom_insert`.

    Its correctness is `FStar.Tactics.CanonCommSemiring.varlist_insert_ok`. *)
val varlist_insert: #a:eqtype -> cr a -> varlist -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let varlist_insert #a r l1 s2 =
  let aone = r.cm_mult.unit in
  monom_insert r aone l1 s2

(*| Multiplies every coefficient of a canonical sum by the scalar `c0`; monomials without coefficient get coefficient `c0`.

    Its correctness is `FStar.Tactics.CanonCommSemiring.canonical_sum_scalar_ok`. *)
val canonical_sum_scalar: #a:Type -> cr a -> a -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec canonical_sum_scalar #a r c0 s =
  let amult = r.cm_mult.mult in
  match s with
  | Cons_monom c l t -> Cons_monom (norm_fully (amult c0 c)) l (canonical_sum_scalar r c0 t)
  | Cons_varlist l t -> Cons_monom c0 l (canonical_sum_scalar r c0 t)
  | Nil_monom -> Nil_monom

(*| Multiplies a canonical sum by the variable list `l0`, re-inserting each resulting monomial at its ordered position.

    Its correctness is `FStar.Tactics.CanonCommSemiring.canonical_sum_scalar2_ok`. *)
val canonical_sum_scalar2: #a:eqtype -> cr a -> varlist
  -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec canonical_sum_scalar2 #a r l0 s =
  match s with
  | Cons_monom c l t ->
    monom_insert r c (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t)
  | Cons_varlist l t ->
    varlist_insert r (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t)
  | Nil_monom -> Nil_monom


(*| Multiplies a canonical sum by the monomial `c0 * l0`, re-inserting each resulting monomial at its ordered position.

    Its correctness is `FStar.Tactics.CanonCommSemiring.canonical_sum_scalar3_ok`. *)
val canonical_sum_scalar3: #a:eqtype -> cr a -> a -> varlist
  -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec canonical_sum_scalar3 #a r c0 l0 s =
  let amult = r.cm_mult.mult in
  match s with
  | Cons_monom c l t ->
    monom_insert r (norm_fully (amult c0 c)) (varlist_merge l0 l)
                 (canonical_sum_scalar3 r c0 l0 t)
  | Cons_varlist l t ->
    monom_insert r c0 (varlist_merge l0 l)
                 (canonical_sum_scalar3 r c0 l0 t)
  | Nil_monom -> s

(*| Multiplies two canonical sums, distributing each monomial of the first over the second and merging the results.

    Its correctness is `FStar.Tactics.CanonCommSemiring.canonical_sum_prod_ok`. *)
val canonical_sum_prod: #a:eqtype -> cr a
  -> canonical_sum a -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec canonical_sum_prod #a r s1 s2 =
  match s1 with
  | Cons_monom c1 l1 t1 ->
    canonical_sum_merge r (canonical_sum_scalar3 r c1 l1 s2)
                          (canonical_sum_prod r t1 s2)
  | Cons_varlist l1 t1 ->
    canonical_sum_merge r (canonical_sum_scalar2 r l1 s2)
                          (canonical_sum_prod r t1 s2)
  | Nil_monom -> s1

///
/// Syntax of concrete semiring polynomials
///

(*| Reflected semiring expressions without additive inverses.

    The constructors are `SPvar i` for the variable of index `i`, `SPconst c` for a constant of the carrier, and `SPplus` and `SPmult` for addition and multiplication. `FStar.Tactics.CanonCommSemiring.interp_sp` gives their meaning; `FStar.Tactics.CanonCommSemiring.spolynomial_of` translates a `FStar.Tactics.CanonCommSemiring.polynomial` to this form. *)
type spolynomial a =
  | SPvar   : index -> spolynomial a
  | SPconst : a -> spolynomial a
  | SPplus  : spolynomial a -> spolynomial a -> spolynomial a
  | SPmult  : spolynomial a -> spolynomial a -> spolynomial a

(*| Computes the canonical sum of a reflected expression without inverses, before simplification.

    Its correctness is `FStar.Tactics.CanonCommSemiring.spolynomial_normalize_ok`; `FStar.Tactics.CanonCommSemiring.spolynomial_simplify` also simplifies the result. *)
val spolynomial_normalize: #a:eqtype -> cr a -> spolynomial a -> canonical_sum a

[@@canon_attr]
let rec spolynomial_normalize #a r p =
  match p with
  | SPvar i -> Cons_varlist (Cons_var i Nil_var) Nil_monom
  | SPconst c -> Cons_monom c Nil_var Nil_monom
  | SPplus l q ->
    canonical_sum_merge r (spolynomial_normalize r l) (spolynomial_normalize r q)
  | SPmult l q ->
    canonical_sum_prod r (spolynomial_normalize r l) (spolynomial_normalize r q)

(*| Simplifies a canonical sum by removing the monomials whose coefficient is `0` and dropping coefficients equal to `1`.

    The tests use the decidable equality of the carrier. Its correctness is `FStar.Tactics.CanonCommSemiring.canonical_sum_simplify_ok`. *)
val canonical_sum_simplify: #a:eqtype -> cr a -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec canonical_sum_simplify #a r s =
  let azero = r.cm_add.unit in
  let aone  = r.cm_mult.unit in
  let aplus = r.cm_add.mult in
  match s with
  | Cons_monom c l t ->
    if norm_fully (c = azero) then canonical_sum_simplify r t
    else
      if norm_fully (c = aone)
      then Cons_varlist l (canonical_sum_simplify r t)
      else Cons_monom c l (canonical_sum_simplify r t)
  | Cons_varlist l t -> Cons_varlist l (canonical_sum_simplify r t)
  | Nil_monom -> s

(*| Computes the simplified canonical sum of a reflected expression without inverses: `FStar.Tactics.CanonCommSemiring.spolynomial_normalize` followed by `FStar.Tactics.CanonCommSemiring.canonical_sum_simplify`.

    Its correctness is `FStar.Tactics.CanonCommSemiring.spolynomial_simplify_ok`. *)
val spolynomial_simplify: #a:eqtype -> cr a -> spolynomial a -> canonical_sum a

[@@canon_attr]
let spolynomial_simplify #a r p =
  canonical_sum_simplify r
    (spolynomial_normalize r p)

///
/// Interpretation of varlists, monomials and canonical sums
///

(*| Variables of the semiring tactic's variable maps: natural numbers, the same as `FStar.Tactics.CanonCommSemiring.index`. *)
type var = nat

(*| Variable maps for semiring reflection: an association list from variables to their values in `a`, together with a default value for unbound variables.

    Each subterm that is neither an addition, a multiplication, an additive inverse nor a literal is turned into a variable bound in the map. The representation is a plain list, which may be slow for large terms. *)
let vmap a = list (var & a) & a

(*| Adds a binding of variable `x` to value `xa` in front of a variable map, shadowing any earlier binding of `x`. *)
let update (#a:Type) (x:var) (xa:a) (vm:vmap a) : vmap a =
  let l, y = vm in (x, xa) :: l, y

(*| Builds the syntax of a list from a list of values, given the syntax `ta` of the element type and a quotation function for the elements. *)
let rec quote_list (#a:Type) (ta:term) (quotea:a -> Tac term) (xs:list a) :
    Tac term =
  match xs with
  | [] -> mk_app (`Nil) [(ta, Q_Implicit)]
  | x::xs' -> mk_app (`Cons) [(ta, Q_Implicit);
                             (quotea x, Q_Explicit);
                             (quote_list ta quotea xs', Q_Explicit)]

(*| Builds the syntax of a variable map, given the syntax `ta` of the carrier type and a quotation function for its values. *)
let quote_vm (#a:Type) (ta: term) (quotea:a -> Tac term) (vm:vmap a) : Tac term =
  let quote_map_entry (p:(nat & a)) : Tac term =
    mk_app (`Mktuple2) [(`nat, Q_Implicit); (ta, Q_Implicit);
      (pack (Tv_Const (C_Int (fst p) (FStar.Sealed.seal Dec))), Q_Explicit);
      (quotea (snd p), Q_Explicit)] in
  let tyentry = mk_e_app (`tuple2) [(`nat); ta] in
  let tlist = quote_list tyentry quote_map_entry (fst vm) in
  let tylist = mk_e_app (`list) [tyentry] in
  mk_app (`Mktuple2) [(tylist, Q_Implicit); (ta, Q_Implicit);
                      (tlist, Q_Explicit); (quotea (snd vm), Q_Explicit)]

(*| Looks up the value of a variable in a variable map, returning the map's default value when the variable is unbound.

    Unbound variables do not arise from the tactic; the default only simplifies the correctness proofs. *)
[@@canon_attr]
let interp_var (#a:Type) (vm:vmap a) (i:index) =
  match List.Tot.Base.assoc i (fst vm) with
  | Some x -> x
  | _ -> snd vm

[@@canon_attr]
private
let rec ivl_aux (#a:Type) (r:cr a) (vm:vmap a) (x:index) (t:varlist)
  : Tot a (decreases t) =
  let amult = r.cm_mult.mult in
  match t with
  | Nil_var -> interp_var vm x
  | Cons_var x' t' -> amult (interp_var vm x) (ivl_aux r vm x' t')

(*| Interprets a variable list as the product of the values of its variables, with the empty list interpreted as `1`. *)
[@@canon_attr]
let interp_vl (#a:Type) (r:cr a) (vm:vmap a) (l:varlist) =
  let aone  = r.cm_mult.unit in
  match l with
  | Nil_var -> aone
  | Cons_var x t -> ivl_aux r vm x t

(*| Interprets the monomial with coefficient `c` and variable list `l` as `c` times the product of the variables of `l`, or `c` alone when `l` is empty. *)
[@@canon_attr]
let interp_m (#a:Type) (r:cr a) (vm:vmap a) (c:a) (l:varlist) =
  let amult = r.cm_mult.mult in
  match l with
  | Nil_var -> c
  | Cons_var x t -> amult c (ivl_aux r vm x t)

(*| Interprets a canonical sum preceded by an already interpreted monomial `x`: the sum of `x` and the monomials of `s`, without a trailing `0`.

    Auxiliary function of `FStar.Tactics.CanonCommSemiring.interp_cs`; `FStar.Tactics.CanonCommSemiring.ics_aux_ok` relates the two. *)
[@@canon_attr]
let rec ics_aux (#a:Type) (r:cr a) (vm:vmap a) (x:a) (s:canonical_sum a)
  : Tot a (decreases s) =
  let aplus = r.cm_add.mult in
  match s with
  | Nil_monom -> x
  | Cons_varlist l t -> aplus x (ics_aux r vm (interp_vl r vm l) t)
  | Cons_monom c l t -> aplus x (ics_aux r vm (interp_m r vm c l) t)

(*| Interprets a canonical sum as the sum of its monomials, with the empty sum interpreted as `0`.

    The sum is built from the first monomial without adding a trailing `0`, so a non-empty canonical sum reads back as a plain ring expression. *)
[@@canon_attr]
let interp_cs (#a:Type) (r:cr a) (vm:vmap a) (s:canonical_sum a) : a =
  let azero = r.cm_add.unit in
  match s with
  | Nil_monom -> azero
  | Cons_varlist l t -> ics_aux r vm (interp_vl r vm l) t
  | Cons_monom c l t -> ics_aux r vm (interp_m r vm c l) t

(*| Interprets a reflected expression without inverses, `FStar.Tactics.CanonCommSemiring.spolynomial`, in a commutative ring, reading variables from the variable map. *)
[@@canon_attr]
let rec interp_sp (#a:Type) (r:cr a) (vm:vmap a) (p:spolynomial a) : a =
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match p with
  | SPconst c -> c
  | SPvar i -> interp_var vm i
  | SPplus p1 p2 -> aplus (interp_sp r vm p1) (interp_sp r vm p2)
  | SPmult p1 p2 -> amult (interp_sp r vm p1) (interp_sp r vm p2)

///
/// Proof of correctness
///

(*| `1` is a left identity of multiplication in a commutative ring.

    Triggered automatically on `r.cm_mult.mult r.cm_mult.unit x`. *)
val mult_one_l (#a:Type) (r:cr a) (x:a) :
  Lemma (r.cm_mult.mult r.cm_mult.unit x == x)
  [SMTPat (r.cm_mult.mult r.cm_mult.unit x)]
let mult_one_l #a r x =
  r.cm_mult.identity x

(*| `1` is a right identity of multiplication in a commutative ring.

    Triggered automatically on `r.cm_mult.mult x r.cm_mult.unit`. *)
val mult_one_r (#a:Type) (r:cr a) (x:a) :
  Lemma (r.cm_mult.mult x r.cm_mult.unit == x)
  [SMTPat (r.cm_mult.mult x r.cm_mult.unit)]
let mult_one_r #a r x =
  r.cm_mult.commutativity r.cm_mult.unit x

(*| `0` is a left zero of multiplication in a commutative ring: `0 * x == 0`.

    Triggered automatically on `r.cm_mult.mult r.cm_add.unit x`. *)
val mult_zero_l (#a:Type) (r:cr a) (x:a) :
  Lemma (r.cm_mult.mult r.cm_add.unit x == r.cm_add.unit)
  [SMTPat (r.cm_mult.mult r.cm_add.unit x)]
let mult_zero_l #a r x =
  r.mult_zero_l x

(*| `0` is a right zero of multiplication in a commutative ring: `x * 0 == 0`.

    Triggered automatically on `r.cm_mult.mult x r.cm_add.unit`. *)
val mult_zero_r (#a:Type) (r:cr a) (x:a) :
  Lemma (r.cm_mult.mult x r.cm_add.unit == r.cm_add.unit)
  [SMTPat (r.cm_mult.mult x r.cm_add.unit)]
let mult_zero_r #a r x =
  r.cm_mult.commutativity x r.cm_add.unit

(*| `0` is a left identity of addition in a commutative ring.

    Triggered automatically on `r.cm_add.mult r.cm_add.unit x`. *)
val add_zero_l (#a:Type) (r:cr a) (x:a) :
  Lemma (r.cm_add.mult r.cm_add.unit x == x)
  [SMTPat (r.cm_add.mult r.cm_add.unit x)]
let add_zero_l #a r x =
  r.cm_add.identity  x

(*| `0` is a right identity of addition in a commutative ring.

    Triggered automatically on `r.cm_add.mult x r.cm_add.unit`. *)
val add_zero_r (#a:Type) (r:cr a) (x:a) :
  Lemma (r.cm_add.mult x r.cm_add.unit == x)
  [SMTPat (r.cm_add.mult x r.cm_add.unit)]
let add_zero_r #a r x =
  r.cm_add.commutativity r.cm_add.unit x

(*| Additive inverses are unique in a commutative ring: if `x + y == 0` then `y == r.opp x`. *)
val opp_unique (#a:Type) (r:cr a) (x y:a) : Lemma
  (requires r.cm_add.mult x y == r.cm_add.unit)
  (ensures  y == r.opp x)
let opp_unique #a r x y =
  let ( + ) = r.cm_add.mult in
  let zero = r.cm_add.unit in
  calc (==) {
    y;
    == { r.add_opp x }
    y + (x + r.opp x);
    == { r.cm_add.associativity y x (r.opp x) }
    (y + x) + r.opp x;
    == { r.cm_add.commutativity x y }
    zero + r.opp x;
    == { }
    r.opp x;
  }

(*| Multiplying by the inverse of `1` gives an additive inverse in a commutative ring: `x + (r.opp 1) * x == 0`.

    Together with `FStar.Tactics.CanonCommSemiring.opp_unique`, this justifies replacing `r.opp x` by `(r.opp 1) * x`, as `FStar.Tactics.CanonCommSemiring.spolynomial_of` does. *)
val add_mult_opp (#a:Type) (r:cr a) (x:a) : Lemma
  (r.cm_add.mult x (r.cm_mult.mult (r.opp r.cm_mult.unit) x) == r.cm_add.unit)
let add_mult_opp #a r x =
  let ( + ) = r.cm_add.mult in
  let ( * ) = r.cm_mult.mult in
  let zero = r.cm_add.unit in
  let one = r.cm_mult.unit in
  calc (==) {
    x + r.opp one * x;
    == { }
    one * x + r.opp one * x;
    == { distribute_right r one (r.opp one) x }
    (one + r.opp one) * x;
    == { r.add_opp one }
    zero * x;
    == { }
    zero;
  }

(*| The private helper used by `FStar.Tactics.CanonCommSemiring.interp_vl` to interpret a non-empty variable list `Cons_var i v` computes the value of variable `i` times the interpretation of `v`. *)
val ivl_aux_ok (#a:Type) (r:cr a) (vm:vmap a) (v:varlist) (i:index) : Lemma
  (ivl_aux r vm i v == r.cm_mult.mult (interp_var vm i) (interp_vl r vm v))
let ivl_aux_ok #a r vm v i = ()

(*| Correctness of `FStar.Tactics.CanonCommSemiring.vm_aux`: the merged variable list is interpreted as the product of the interpretations of `Cons_var v t` and `l`. *)
val vm_aux_ok (#a:eqtype) (r:cr a) (vm:vmap a) (v:index) (t l:varlist) :
  Lemma
  (ensures
    interp_vl r vm (vm_aux v t l) ==
    r.cm_mult.mult (interp_vl r vm (Cons_var v t)) (interp_vl r vm l))
  (decreases %[t; l; 1])

(*| Correctness of `FStar.Tactics.CanonCommSemiring.varlist_merge`: the merged variable list is interpreted as the product of the interpretations of the two inputs. *)
val varlist_merge_ok (#a:eqtype) (r:cr a) (vm:vmap a) (x y:varlist) :
  Lemma
  (ensures
    interp_vl r vm (varlist_merge x y) ==
    r.cm_mult.mult (interp_vl r vm x) (interp_vl r vm y))
  (decreases %[x; y; 0])

let rec varlist_merge_ok #a r vm x y =
  let amult = r.cm_mult.mult in
  match x, y with
  | Cons_var v1 t1, Nil_var -> ()
  | Cons_var v1 t1, Cons_var v2 t2 ->
    if v1 < v2
    then
      begin
      varlist_merge_ok r vm t1 y;
      assert (
        interp_vl r vm (varlist_merge x y) ==
        amult (interp_var vm v1) (amult (interp_vl r vm t1) (interp_vl r vm y)));
      r.cm_mult.associativity
        (interp_var vm v1) (interp_vl r vm t1) (interp_vl r vm y)
      end
    else
      vm_aux_ok r vm v1 t1 y
  | Nil_var, _ -> ()
and vm_aux_ok #a r vm v1 t1 l2 =
  match l2 with
  | Cons_var v2 t2 ->
    if v1 < v2
    then
      begin
      varlist_merge_ok r vm t1 l2;
      r.cm_mult.associativity
        (interp_var vm v1) (interp_vl r vm t1) (interp_vl r vm l2)
      end
    else
      begin
      vm_aux_ok r vm v1 t1 t2;
      calc (==) {
        interp_vl r vm (Cons_var v2 (vm_aux v1 t1 t2));
        == { }
        ivl_aux r vm v2 (vm_aux v1 t1 t2);
        == { }
        r.cm_mult.mult (interp_var vm v2) (interp_vl r vm (vm_aux v1 t1 t2));
        == { }
        r.cm_mult.mult (interp_var vm v2) (r.cm_mult.mult (interp_vl r vm (Cons_var v1 t1)) (interp_vl r vm t2));
        == { r.cm_mult.commutativity
               (interp_vl r vm (Cons_var v1 t1)) (interp_vl r vm t2) }
        r.cm_mult.mult (interp_var vm v2)
          (r.cm_mult.mult (interp_vl r vm t2) (interp_vl r vm (Cons_var v1 t1)) );
        == { r.cm_mult.associativity
              (interp_var vm v2)
              (interp_vl r vm t2) (interp_vl r vm (Cons_var v1 t1)) }
        r.cm_mult.mult
         (r.cm_mult.mult (interp_var vm v2) (interp_vl r vm t2))
         (interp_vl r vm (Cons_var v1 t1));
        == { r.cm_mult.commutativity
            (interp_vl r vm (Cons_var v1 t1)) (interp_vl r vm (Cons_var v2 t2)) }
        r.cm_mult.mult (interp_vl r vm (Cons_var v1 t1)) (interp_vl r vm (Cons_var v2 t2));
      }
      end
  | _ -> ()

(*| Relates `FStar.Tactics.CanonCommSemiring.ics_aux` to `FStar.Tactics.CanonCommSemiring.interp_cs`: `ics_aux r vm x s` is the sum of `x` and the interpretation of `s`. *)
val ics_aux_ok: #a:eqtype -> r:cr a -> vm:vmap a -> x:a -> s:canonical_sum a ->
  Lemma (ensures ics_aux r vm x s == r.cm_add.mult x (interp_cs r vm s))
  (decreases s)
let rec ics_aux_ok #a r vm x s =
  match s with
  | Nil_monom -> ()
  | Cons_varlist l t ->
    ics_aux_ok r vm (interp_vl r vm l) t
  | Cons_monom c l t ->
    ics_aux_ok r vm (interp_m r vm c l) t

(*| A monomial with coefficient `x` and variable list `l` is interpreted as `x` times the interpretation of `l`, including when `l` is empty. *)
val interp_m_ok: #a:eqtype -> r:cr a -> vm:vmap a -> x:a -> l:varlist ->
  Lemma (interp_m r vm x l == r.cm_mult.mult x (interp_vl r vm l))
let interp_m_ok #a r vm x l = ()

(*| Rearranges a sum of four terms in a commutative ring: `(w + x) + (y + z) == (w + y) + (x + z)`. *)
val aplus_assoc_4: #a:Type -> r:cr a -> w:a -> x:a -> y:a -> z:a -> Lemma
  (let aplus = r.cm_add.mult in
   aplus (aplus w x) (aplus y z) == aplus (aplus w y) (aplus x z))
let aplus_assoc_4 #a r w x y z =
  let aplus = r.cm_add.mult in
  let assoc = r.cm_add.associativity in
  let comm = r.cm_add.commutativity in
  calc (==) {
    aplus (aplus w x) (aplus y z);
    == { assoc w x (aplus y z) }
    aplus w (aplus x (aplus y z));
    == { comm x (aplus y z) }
    aplus w (aplus (aplus y z) x);
    == { assoc w (aplus y z) x }
    aplus (aplus w (aplus y z)) x;
    == { assoc w y z }
    aplus (aplus (aplus w y) z) x;
    == { assoc (aplus w y) z x }
    aplus (aplus w y) (aplus z x);
    == { comm z x }
    aplus (aplus w y) (aplus x z);
  }

(*| Correctness of `FStar.Tactics.CanonCommSemiring.canonical_sum_merge`: the merged sum is interpreted as the sum of the interpretations of the two inputs. *)
val canonical_sum_merge_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> s1:canonical_sum a -> s2:canonical_sum a ->
  Lemma
  (ensures
    interp_cs r vm (canonical_sum_merge r s1 s2) ==
    r.cm_add.mult (interp_cs r vm s1) (interp_cs r vm s2))
  (decreases %[s1; s2; 0])

(*| Correctness of `FStar.Tactics.CanonCommSemiring.csm_aux`: the result is interpreted as the sum of the interpretations of `Cons_monom c1 l1 t1` and `s2`. *)
val csm_aux_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> c1:a -> l1:varlist -> t1:canonical_sum a -> s2:canonical_sum a ->
  Lemma
  (ensures
    interp_cs r vm (csm_aux r c1 l1 t1 s2) ==
    r.cm_add.mult (interp_cs r vm (Cons_monom c1 l1 t1)) (interp_cs r vm s2))
  (decreases %[t1; s2; 1])

let rec canonical_sum_merge_ok #a r vm s1 s2 =
  let aone  = r.cm_mult.unit in
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match s1 with
  | Cons_monom c1 l1 t1 -> csm_aux_ok #a r vm c1 l1 t1 s2
  | Cons_varlist l1 t1  ->
    calc (==) {
      interp_cs r vm (canonical_sum_merge r s1 s2);
      == { }
      interp_cs r vm (csm_aux r aone l1 t1 s2);
      == { csm_aux_ok #a r vm aone l1 t1 s2 }
      aplus (interp_cs r vm (Cons_monom aone l1 t1))
            (interp_cs r vm s2);
      == { ics_aux_ok r vm (interp_vl r vm l1) t1 }
      aplus (interp_cs r vm (Cons_varlist l1 t1))
            (interp_cs r vm s2);
    }
  | Nil_monom -> ()
and csm_aux_ok #a r vm c1 l1 t1 s2 =
  let aplus = r.cm_add.mult in
  let aone  = r.cm_mult.unit in
  let amult = r.cm_mult.mult in
  match s2 with
  | Nil_monom -> ()
  | Cons_monom c2 l2 t2 ->
    let s1 = Cons_monom c1 l1 t1 in
    if l1 = l2 then
    begin
    calc (==) {
      interp_cs r vm (csm_aux r c1 l1 t1 s2);
      == { }
      ics_aux r vm (interp_m r vm (aplus c1 c2) l1)
                   (canonical_sum_merge r t1 t2);
      == { ics_aux_ok r vm (interp_m r vm (aplus c1 c2) l1)
                           (canonical_sum_merge r t1 t2) }
      aplus (interp_m r vm (aplus c1 c2) l1)
            (interp_cs r vm (canonical_sum_merge r t1 t2));
      == { interp_m_ok r vm (aplus c1 c2) l1 }
      aplus (amult (aplus c1 c2) (interp_vl r vm l1))
            (interp_cs r vm (canonical_sum_merge r t1 t2));
      == { canonical_sum_merge_ok r vm t1 t2 }
      aplus (amult (aplus c1 c2) (interp_vl r vm l1))
            (aplus (interp_cs r vm t1) (interp_cs r vm t2));
      == { distribute_right r c1 c2 (interp_vl r vm l1) }
      aplus (aplus (amult c1 (interp_vl r vm l1))
                   (amult c2 (interp_vl r vm l2)))
            (aplus (interp_cs r vm t1)
                   (interp_cs r vm t2));
      == { aplus_assoc_4 r
             (amult c1 (interp_vl r vm l1))
             (amult c2 (interp_vl r vm l2))
             (interp_cs r vm t1)
             (interp_cs r vm t2) }
      aplus (aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm t1))
            (aplus (amult c2 (interp_vl r vm l2)) (interp_cs r vm t2));
      == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
           interp_m_ok r vm c1 l1 }
      aplus (interp_cs r vm s1)
            (aplus (amult c2 (interp_vl r vm l2)) (interp_cs r vm t2));
      == { ics_aux_ok r vm (amult c2 (interp_vl r vm l2)) t2;
           interp_m_ok r vm c2 l2 }
      aplus (interp_cs r vm s1) (interp_cs r vm s2);
    }
    end
    else if varlist_lt l1 l2 then
    begin
    calc (==) {
      interp_cs r vm (canonical_sum_merge r s1 s2);
      == { }
      ics_aux r vm (interp_m r vm c1 l1)
                   (canonical_sum_merge r t1 s2);
      == { ics_aux_ok r vm (interp_m r vm c1 l1)
                           (canonical_sum_merge r t1 s2) }
      aplus (interp_m r vm c1 l1)
            (interp_cs r vm (canonical_sum_merge r t1 s2));
      == { interp_m_ok r vm c1 l1 }
      aplus (amult c1 (interp_vl r vm l1))
            (interp_cs r vm (canonical_sum_merge r t1 s2));
      == { canonical_sum_merge_ok r vm t1 s2 }
      aplus (amult c1 (interp_vl r vm l1))
            (aplus (interp_cs r vm t1) (interp_cs r vm s2));
      == { r.cm_add.associativity
             (amult c1 (interp_vl r vm l1))
             (interp_cs r vm t1)
             (interp_cs r vm s2)
         }
      aplus (aplus (amult c1 (interp_vl r vm l1))
                   (interp_cs r vm t1))
            (interp_cs r vm s2);
      == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
           interp_m_ok r vm c1 l1 }
      aplus (interp_cs r vm s1) (interp_cs r vm s2);
    }
    end
    else
    begin
    calc (==) {
      interp_cs r vm (csm_aux r c1 l1 t1 s2);
      == { }
      ics_aux r vm (interp_m r vm c2 l2)
                   (csm_aux r c1 l1 t1 t2);
      == { ics_aux_ok r vm (interp_m r vm c2 l2)
                           (csm_aux r c1 l1 t1 t2) }
      aplus (interp_m r vm c2 l2)
            (interp_cs r vm (csm_aux r c1 l1 t1 t2));
      == { interp_m_ok r vm c2 l2 }
      aplus (amult c2 (interp_vl r vm l2))
            (interp_cs r vm (csm_aux r c1 l1 t1 t2));
      == { csm_aux_ok r vm c1 l1 t1 t2 }
      aplus (amult c2 (interp_vl r vm l2))
            (aplus (interp_cs r vm s1) (interp_cs r vm t2));
      == { r.cm_add.commutativity (interp_cs r vm s1) (interp_cs r vm t2) }
      aplus (amult c2 (interp_vl r vm l2))
            (aplus (interp_cs r vm t2) (interp_cs r vm s1));
      == { r.cm_add.associativity
             (amult c2 (interp_vl r vm l2))
             (interp_cs r vm t2)
             (interp_cs r vm s1)
         }
      aplus (aplus (amult c2 (interp_vl r vm l2))
                   (interp_cs r vm t2))
            (interp_cs r vm s1);
      == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
           interp_m_ok r vm c1 l1 }
      aplus (interp_cs r vm s2) (interp_cs r vm s1);
      == { r.cm_add.commutativity (interp_cs r vm s1) (interp_cs r vm s2) }
      aplus (interp_cs r vm s1) (interp_cs r vm s2);
    }
    end
  | Cons_varlist l2 t2 -> // Same as Cons_monom with c2 = aone
    let c2 = aone in
    let s1 = Cons_monom c1 l1 t1 in
    if l1 = l2 then
    begin
    calc (==) {
      interp_cs r vm (csm_aux r c1 l1 t1 s2);
      == { }
      ics_aux r vm (interp_m r vm (aplus c1 c2) l1)
                   (canonical_sum_merge r t1 t2);
      == { ics_aux_ok r vm (interp_m r vm (aplus c1 c2) l1)
                           (canonical_sum_merge r t1 t2) }
      aplus (interp_m r vm (aplus c1 c2) l1)
            (interp_cs r vm (canonical_sum_merge r t1 t2));
      == { interp_m_ok r vm (aplus c1 c2) l1 }
      aplus (amult (aplus c1 c2) (interp_vl r vm l1))
            (interp_cs r vm (canonical_sum_merge r t1 t2));
      == { canonical_sum_merge_ok r vm t1 t2 }
      aplus (amult (aplus c1 c2) (interp_vl r vm l1))
            (aplus (interp_cs r vm t1) (interp_cs r vm t2));
      == { distribute_right r c1 c2 (interp_vl r vm l1) }
      aplus (aplus (amult c1 (interp_vl r vm l1))
                   (amult c2 (interp_vl r vm l2)))
            (aplus (interp_cs r vm t1)
                   (interp_cs r vm t2));
      == { aplus_assoc_4 r
             (amult c1 (interp_vl r vm l1))
             (amult c2 (interp_vl r vm l2))
             (interp_cs r vm t1)
             (interp_cs r vm t2) }
      aplus (aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm t1))
            (aplus (amult c2 (interp_vl r vm l2)) (interp_cs r vm t2));
      == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
           interp_m_ok r vm c1 l1 }
      aplus (interp_cs r vm s1)
            (aplus (amult c2 (interp_vl r vm l2)) (interp_cs r vm t2));
      == { ics_aux_ok r vm (amult c2 (interp_vl r vm l2)) t2;
           interp_m_ok r vm c2 l2 }
      aplus (interp_cs r vm s1) (interp_cs r vm s2);
    }
    end
    else if varlist_lt l1 l2 then
    begin
    calc (==) {
      interp_cs r vm (canonical_sum_merge r s1 s2);
      == { }
      ics_aux r vm (interp_m r vm c1 l1)
                   (canonical_sum_merge r t1 s2);
      == { ics_aux_ok r vm (interp_m r vm c1 l1)
                           (canonical_sum_merge r t1 s2) }
      aplus (interp_m r vm c1 l1)
            (interp_cs r vm (canonical_sum_merge r t1 s2));
      == { interp_m_ok r vm c1 l1 }
      aplus (amult c1 (interp_vl r vm l1))
            (interp_cs r vm (canonical_sum_merge r t1 s2));
      == { canonical_sum_merge_ok r vm t1 s2 }
      aplus (amult c1 (interp_vl r vm l1))
            (aplus (interp_cs r vm t1) (interp_cs r vm s2));
      == { r.cm_add.associativity
             (amult c1 (interp_vl r vm l1))
             (interp_cs r vm t1)
             (interp_cs r vm s2)
         }
      aplus (aplus (amult c1 (interp_vl r vm l1))
                   (interp_cs r vm t1))
            (interp_cs r vm s2);
      == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
           interp_m_ok r vm c1 l1 }
      aplus (interp_cs r vm s1) (interp_cs r vm s2);
    }
    end
    else
    begin
    calc (==) {
      interp_cs r vm (csm_aux r c1 l1 t1 s2);
      == { }
      ics_aux r vm (interp_m r vm c2 l2)
                   (csm_aux r c1 l1 t1 t2);
      == { ics_aux_ok r vm (interp_m r vm c2 l2)
                           (csm_aux r c1 l1 t1 t2) }
      aplus (interp_m r vm c2 l2)
            (interp_cs r vm (csm_aux r c1 l1 t1 t2));
      == { interp_m_ok r vm c2 l2 }
      aplus (amult c2 (interp_vl r vm l2))
            (interp_cs r vm (csm_aux r c1 l1 t1 t2));
      == { csm_aux_ok r vm c1 l1 t1 t2 }
      aplus (amult c2 (interp_vl r vm l2))
            (aplus (interp_cs r vm s1) (interp_cs r vm t2));
      == { r.cm_add.commutativity (interp_cs r vm s1) (interp_cs r vm t2) }
      aplus (amult c2 (interp_vl r vm l2))
            (aplus (interp_cs r vm t2) (interp_cs r vm s1));
      == { r.cm_add.associativity
             (amult c2 (interp_vl r vm l2))
             (interp_cs r vm t2)
             (interp_cs r vm s1)
         }
      aplus (aplus (amult c2 (interp_vl r vm l2))
                   (interp_cs r vm t2))
            (interp_cs r vm s1);
      == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
           interp_m_ok r vm c1 l1 }
      aplus (interp_cs r vm s2) (interp_cs r vm s1);
      == { r.cm_add.commutativity (interp_cs r vm s1) (interp_cs r vm s2) }
      aplus (interp_cs r vm s1) (interp_cs r vm s2);
    }
    end

(*| Correctness of `FStar.Tactics.CanonCommSemiring.monom_insert`: the result is interpreted as `c1` times the interpretation of `l1`, plus the interpretation of `s2`. *)
val monom_insert_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> c1:a -> l1:varlist -> s2:canonical_sum a ->
  Lemma
  (interp_cs r vm (monom_insert r c1 l1 s2) ==
   r.cm_add.mult (r.cm_mult.mult c1 (interp_vl r vm l1)) (interp_cs r vm s2))
let rec monom_insert_ok #a r vm c1 l1 s2 =
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  let aone  = r.cm_mult.unit in
  match s2 with
  | Cons_monom c2 l2 t2 ->
    if l1 = l2
    then
      calc (==) {
        interp_cs r vm (monom_insert r c1 l1 s2);
        == { }
        interp_cs r vm (Cons_monom (aplus c1 c2) l1 t2);
        == { }
        ics_aux r vm (interp_m r vm (aplus c1 c2) l1) t2;
        == { ics_aux_ok r vm (interp_m r vm (aplus c1 c2) l1) t2 }
        aplus (interp_m r vm (aplus c1 c2) l1) (interp_cs r vm t2);
        == { interp_m_ok r vm (aplus c1 c2) l1 }
        aplus (amult (aplus c1 c2) (interp_vl r vm l2)) (interp_cs r vm t2);
        == { distribute_right r c1 c2 (interp_vl r vm l2) }
        aplus (aplus (amult c1 (interp_vl r vm l1))
                     (amult c2 (interp_vl r vm l2)))
              (interp_cs r vm t2);
        == { r.cm_add.associativity
               (amult c1 (interp_vl r vm l1))
               (amult c2 (interp_vl r vm l2))
               (interp_cs r vm t2) }
        aplus (amult c1 (interp_vl r vm l1))
              (aplus (amult c2 (interp_vl r vm l2))
                     (interp_cs r vm t2));
        == { ics_aux_ok r vm (interp_m r vm c2 l2) t2 }
        aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm s2);
      }
    else
     if varlist_lt l1 l2 then ()
     else
       calc (==) {
        interp_cs r vm (monom_insert r c1 l1 s2);
        == { }
        interp_cs r vm (Cons_monom c2 l2 (monom_insert r c1 l1 t2));
        == { }
        aplus (amult c2 (interp_vl r vm l2))
              (interp_cs r vm (monom_insert r c1 l1 t2));
        == { monom_insert_ok r vm c1 l1 t2 }
        aplus (amult c2 (interp_vl r vm l2))
              (aplus (amult c1 (interp_vl r vm l1))
                     (interp_cs r vm t2));
        == { r.cm_add.commutativity
               (amult c1 (interp_vl r vm l1))
               (interp_cs r vm t2) }
        aplus (amult c2 (interp_vl r vm l2))
              (aplus (interp_cs r vm t2)
                     (amult c1 (interp_vl r vm l1)));
        == { r.cm_add.associativity
              (amult c2 (interp_vl r vm l2))
              (interp_cs r vm t2)
              (amult c1 (interp_vl r vm l1)) }
        aplus (aplus (amult c2 (interp_vl r vm l2))
                     (interp_cs r vm t2))
              (amult c1 (interp_vl r vm l1));
        == { ics_aux_ok r vm (interp_m r vm c2 l2) t2 }
        aplus (interp_cs r vm s2) (amult c1 (interp_vl r vm l1));
        == { r.cm_add.commutativity
              (interp_cs r vm s2)
              (amult c1 (interp_vl r vm l1)) }
        aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm s2);
       }
  | Cons_varlist l2 t2 -> // Same as Cons_monom with c2 = aone
    let c2 = aone in
    if l1 = l2
    then
      calc (==) {
        interp_cs r vm (monom_insert r c1 l1 s2);
        == { }
        interp_cs r vm (Cons_monom (aplus c1 c2) l1 t2);
        == { }
        ics_aux r vm (interp_m r vm (aplus c1 c2) l1) t2;
        == { ics_aux_ok r vm (interp_m r vm (aplus c1 c2) l1) t2 }
        aplus (interp_m r vm (aplus c1 c2) l1) (interp_cs r vm t2);
        == { interp_m_ok r vm (aplus c1 c2) l1 }
        aplus (amult (aplus c1 c2) (interp_vl r vm l2)) (interp_cs r vm t2);
        == { distribute_right r c1 c2 (interp_vl r vm l2) }
        aplus (aplus (amult c1 (interp_vl r vm l1))
                     (amult c2 (interp_vl r vm l2)))
              (interp_cs r vm t2);
        == { r.cm_add.associativity
               (amult c1 (interp_vl r vm l1))
               (amult c2 (interp_vl r vm l2))
               (interp_cs r vm t2) }
        aplus (amult c1 (interp_vl r vm l1))
              (aplus (amult c2 (interp_vl r vm l2))
                     (interp_cs r vm t2));
        == { ics_aux_ok r vm (interp_m r vm c2 l2) t2 }
        aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm s2);
      }
    else
     if varlist_lt l1 l2 then ()
     else
       calc (==) {
        interp_cs r vm (monom_insert r c1 l1 s2);
        == { }
        interp_cs r vm (Cons_monom c2 l2 (monom_insert r c1 l1 t2));
        == { }
        aplus (amult c2 (interp_vl r vm l2))
              (interp_cs r vm (monom_insert r c1 l1 t2));
        == { monom_insert_ok r vm c1 l1 t2 }
        aplus (amult c2 (interp_vl r vm l2))
              (aplus (amult c1 (interp_vl r vm l1))
                     (interp_cs r vm t2));
        == { r.cm_add.commutativity
               (amult c1 (interp_vl r vm l1))
               (interp_cs r vm t2) }
        aplus (amult c2 (interp_vl r vm l2))
              (aplus (interp_cs r vm t2)
                     (amult c1 (interp_vl r vm l1)));
        == { r.cm_add.associativity
              (amult c2 (interp_vl r vm l2))
              (interp_cs r vm t2)
              (amult c1 (interp_vl r vm l1)) }
        aplus (aplus (amult c2 (interp_vl r vm l2))
                     (interp_cs r vm t2))
              (amult c1 (interp_vl r vm l1));
        == { ics_aux_ok r vm (interp_m r vm c2 l2) t2 }
        aplus (interp_cs r vm s2) (amult c1 (interp_vl r vm l1));
        == { r.cm_add.commutativity
              (interp_cs r vm s2)
              (amult c1 (interp_vl r vm l1)) }
        aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm s2);
       }
  | Nil_monom -> ()

(*| Correctness of `FStar.Tactics.CanonCommSemiring.varlist_insert`: the result is interpreted as the interpretation of `l1` plus the interpretation of `s2`. *)
val varlist_insert_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> l1:varlist -> s2:canonical_sum a ->
  Lemma (interp_cs r vm (varlist_insert r l1 s2) ==
         r.cm_add.mult (interp_vl r vm l1) (interp_cs r vm s2))
let varlist_insert_ok #a r vm l1 s2 =
  let aone = r.cm_mult.unit in
  monom_insert_ok r vm aone l1 s2

(*| Correctness of `FStar.Tactics.CanonCommSemiring.canonical_sum_scalar`: the result is interpreted as `c0` times the interpretation of `s`. *)
val canonical_sum_scalar_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> c0:a -> s:canonical_sum a ->
  Lemma (
    interp_cs r vm (canonical_sum_scalar r c0 s) ==
    r.cm_mult.mult c0 (interp_cs r vm s))
let rec canonical_sum_scalar_ok #a r vm c0 s =
  let aone  = r.cm_mult.unit in
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match s with
  | Cons_monom c l t ->
    calc (==) {
      interp_cs r vm (canonical_sum_scalar r c0 s);
      == { }
      interp_cs r vm (Cons_monom (amult c0 c) l (canonical_sum_scalar r c0 t));
      == { }
      aplus (amult (amult c0 c) (interp_vl r vm l))
            (interp_cs r vm (canonical_sum_scalar r c0 t));
      == { r.cm_mult.associativity c0 c (interp_vl r vm l) }
      aplus (amult c0 (amult c (interp_vl r vm l)))
            (interp_cs r vm (canonical_sum_scalar r c0 t));
      == { canonical_sum_scalar_ok r vm c0 t }
      aplus (amult c0 (amult c (interp_vl r vm l)))
            (amult c0 (interp_cs r vm t));
      == { r.distribute c0 (amult c (interp_vl r vm l))
                              (interp_cs r vm t) }
      amult c0 (aplus (amult c (interp_vl r vm l)) (interp_cs r vm t));
      == { }
      amult c0 (interp_cs r vm s);
    }
  | Cons_varlist l t -> // Same as Cons_monom c l t with c = r.cm_mult.unit
    let c = aone in
        calc (==) {
      interp_cs r vm (canonical_sum_scalar r c0 s);
      == { }
      interp_cs r vm (Cons_monom (amult c0 c) l (canonical_sum_scalar r c0 t));
      == { }
      aplus (amult (amult c0 c) (interp_vl r vm l))
            (interp_cs r vm (canonical_sum_scalar r c0 t));
      == { r.cm_mult.associativity c0 c (interp_vl r vm l) }
      aplus (amult c0 (amult c (interp_vl r vm l)))
            (interp_cs r vm (canonical_sum_scalar r c0 t));
      == { canonical_sum_scalar_ok r vm c0 t }
      aplus (amult c0 (amult c (interp_vl r vm l)))
            (amult c0 (interp_cs r vm t));
      == { r.distribute c0 (amult c (interp_vl r vm l))
                              (interp_cs r vm t) }
      amult c0 (aplus (amult c (interp_vl r vm l)) (interp_cs r vm t));
      == { }
      amult c0 (interp_cs r vm s);
    }
  | Nil_monom -> ()

(*| Correctness of `FStar.Tactics.CanonCommSemiring.canonical_sum_scalar2`: the result is interpreted as the interpretation of `l0` times the interpretation of `s`. *)
val canonical_sum_scalar2_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> l0:varlist -> s:canonical_sum a ->
  Lemma (
    interp_cs r vm (canonical_sum_scalar2 r l0 s) ==
    r.cm_mult.mult (interp_vl r vm l0) (interp_cs r vm s))
let rec canonical_sum_scalar2_ok #a r vm l0 s =
  let aone  = r.cm_mult.unit in
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match s with
  | Cons_monom c l t ->
    calc (==) {
      interp_cs r vm (canonical_sum_scalar2 r l0 s);
      == { }
      interp_cs r vm
        (monom_insert r c (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t));
      == { monom_insert_ok r vm c (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t) }
      aplus (amult c (interp_vl r vm (varlist_merge l0 l)))
            (interp_cs r vm (canonical_sum_scalar2 r l0 t));
      == { varlist_merge_ok r vm l0 l }
      aplus (amult c (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (interp_cs r vm (canonical_sum_scalar2 r l0 t));
      == { canonical_sum_scalar2_ok r vm l0 t }
      aplus (amult c (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.cm_mult.associativity c (interp_vl r vm l0)
             (interp_vl r vm l) }
      aplus (amult (amult c (interp_vl r vm l0)) (interp_vl r vm l))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.cm_mult.commutativity (interp_vl r vm l0) c }
      aplus (amult (amult (interp_vl r vm l0) c) (interp_vl r vm l))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.cm_mult.associativity (interp_vl r vm l0) c (interp_vl r vm l) }
      aplus (amult (interp_vl r vm l0) (amult c (interp_vl r vm l)))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.distribute (interp_vl r vm l0)
             (amult c (interp_vl r vm l)) (interp_cs r vm t) }
      amult (interp_vl r vm l0)
            (aplus (amult c (interp_vl r vm l)) (interp_cs r vm t));
      == {  }
      amult (interp_vl r vm l0) (interp_cs r vm s);
    }
  | Cons_varlist l t -> // Same as Cons_monom c l t with c = aone
    let c = aone in
    calc (==) {
      interp_cs r vm (canonical_sum_scalar2 r l0 s);
      == { }
      interp_cs r vm
        (monom_insert r c (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t));
      == { monom_insert_ok r vm c (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t) }
      aplus (amult c (interp_vl r vm (varlist_merge l0 l)))
            (interp_cs r vm (canonical_sum_scalar2 r l0 t));
      == { varlist_merge_ok r vm l0 l }
      aplus (amult c (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (interp_cs r vm (canonical_sum_scalar2 r l0 t));
      == { canonical_sum_scalar2_ok r vm l0 t }
      aplus (amult c (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.cm_mult.associativity c (interp_vl r vm l0)
             (interp_vl r vm l) }
      aplus (amult (amult c (interp_vl r vm l0)) (interp_vl r vm l))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.cm_mult.commutativity (interp_vl r vm l0) c }
      aplus (amult (amult (interp_vl r vm l0) c) (interp_vl r vm l))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.cm_mult.associativity (interp_vl r vm l0) c (interp_vl r vm l) }
      aplus (amult (interp_vl r vm l0) (amult c (interp_vl r vm l)))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.distribute (interp_vl r vm l0)
             (amult c (interp_vl r vm l)) (interp_cs r vm t) }
      amult (interp_vl r vm l0)
            (aplus (amult c (interp_vl r vm l)) (interp_cs r vm t));
      == {  }
      amult (interp_vl r vm l0) (interp_cs r vm s);
    }
  | Nil_monom -> ()

(*| Correctness of `FStar.Tactics.CanonCommSemiring.canonical_sum_scalar3`: the result is interpreted as `c0` times the interpretation of `l0`, times the interpretation of `s`. *)
val canonical_sum_scalar3_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> c0:a -> l0:varlist -> s:canonical_sum a ->
  Lemma (
    interp_cs r vm (canonical_sum_scalar3 r c0 l0 s) ==
    r.cm_mult.mult (r.cm_mult.mult c0 (interp_vl r vm l0)) (interp_cs r vm s))
let rec canonical_sum_scalar3_ok #a r vm c0 l0 s =
  let aone  = r.cm_mult.unit in
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match s with
  | Cons_monom c l t ->
    calc (==) {
      interp_cs r vm (canonical_sum_scalar3 r c0 l0 s);
      == { }
      interp_cs r vm
        (monom_insert r (amult c0 c) (varlist_merge l0 l)
          (canonical_sum_scalar3 r c0 l0 t));
      == { monom_insert_ok r vm (amult c0 c) (varlist_merge l0 l) (canonical_sum_scalar3 r c0 l0 t) }
      aplus (amult (amult c0 c) (interp_vl r vm (varlist_merge l0 l)))
            (interp_cs r vm (canonical_sum_scalar3 r c0 l0 t));
      == { varlist_merge_ok r vm l0 l }
      aplus (amult (amult c0 c) (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (interp_cs r vm (canonical_sum_scalar3 r c0 l0 t));
      == { canonical_sum_scalar3_ok r vm c0 l0 t }
      aplus (amult (amult c0 c) (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.associativity (amult c0 c)
             (interp_vl r vm l0) (interp_vl r vm l) }
      aplus (amult (amult (amult c0 c) (interp_vl r vm l0)) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.commutativity c0 c }
      aplus (amult (amult (amult c c0) (interp_vl r vm l0)) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.associativity c c0 (interp_vl r vm l0) }
      aplus (amult (amult c (amult c0 (interp_vl r vm l0))) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.commutativity c (amult c0 (interp_vl r vm l0)) }
      aplus (amult (amult (amult c0 (interp_vl r vm l0)) c) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.associativity (amult c0 (interp_vl r vm l0)) c (interp_vl r vm l) }
      aplus (amult (amult c0 (interp_vl r vm l0)) (amult c (interp_vl r vm l)))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.distribute (amult c0 (interp_vl r vm l0))
             (amult c (interp_vl r vm l)) (interp_cs r vm t) }
      amult (amult c0 (interp_vl r vm l0))
            (aplus (amult c (interp_vl r vm l)) (interp_cs r vm t));
      == {  }
      amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm s);
    }
  | Cons_varlist l t -> // Same as Cons_monom c l t with c = aone
    let c = aone in
    calc (==) {
      interp_cs r vm (canonical_sum_scalar3 r c0 l0 s);
      == { }
      interp_cs r vm
        (monom_insert r (amult c0 c) (varlist_merge l0 l)
          (canonical_sum_scalar3 r c0 l0 t));
      == { monom_insert_ok r vm (amult c0 c) (varlist_merge l0 l) (canonical_sum_scalar3 r c0 l0 t) }
      aplus (amult (amult c0 c) (interp_vl r vm (varlist_merge l0 l)))
            (interp_cs r vm (canonical_sum_scalar3 r c0 l0 t));
      == { varlist_merge_ok r vm l0 l }
      aplus (amult (amult c0 c) (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (interp_cs r vm (canonical_sum_scalar3 r c0 l0 t));
      == { canonical_sum_scalar3_ok r vm c0 l0 t }
      aplus (amult (amult c0 c) (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.associativity (amult c0 c)
             (interp_vl r vm l0) (interp_vl r vm l) }
      aplus (amult (amult (amult c0 c) (interp_vl r vm l0)) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.commutativity c0 c }
      aplus (amult (amult (amult c c0) (interp_vl r vm l0)) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.associativity c c0 (interp_vl r vm l0) }
      aplus (amult (amult c (amult c0 (interp_vl r vm l0))) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.commutativity c (amult c0 (interp_vl r vm l0)) }
      aplus (amult (amult (amult c0 (interp_vl r vm l0)) c) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.associativity (amult c0 (interp_vl r vm l0)) c (interp_vl r vm l) }
      aplus (amult (amult c0 (interp_vl r vm l0)) (amult c (interp_vl r vm l)))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.distribute (amult c0 (interp_vl r vm l0))
             (amult c (interp_vl r vm l)) (interp_cs r vm t) }
      amult (amult c0 (interp_vl r vm l0))
            (aplus (amult c (interp_vl r vm l)) (interp_cs r vm t));
      == {  }
      amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm s);
    }
  | Nil_monom -> ()

(*| Correctness of `FStar.Tactics.CanonCommSemiring.canonical_sum_prod`: the result is interpreted as the product of the interpretations of the two inputs. *)
val canonical_sum_prod_ok: #a:eqtype -> r:cr a -> vm:vmap a ->
  s1:canonical_sum a -> s2:canonical_sum a ->
  Lemma (interp_cs r vm (canonical_sum_prod r s1 s2) ==
         r.cm_mult.mult (interp_cs r vm s1) (interp_cs r vm s2))
let rec canonical_sum_prod_ok #a r vm s1 s2 =
  let aone  = r.cm_mult.unit in
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match s1 with
  | Cons_monom c1 l1 t1 ->
    calc (==) {
      interp_cs r vm (canonical_sum_prod r s1 s2);
      == { }
      interp_cs r vm
        (canonical_sum_merge r (canonical_sum_scalar3 r c1 l1 s2)
                               (canonical_sum_prod r t1 s2));
      == { canonical_sum_merge_ok r vm
             (canonical_sum_scalar3 r c1 l1 s2)
             (canonical_sum_prod r t1 s2) }
      aplus (interp_cs r vm (canonical_sum_scalar3 r c1 l1 s2))
            (interp_cs r vm (canonical_sum_prod r t1 s2));
      == { canonical_sum_scalar3_ok r vm c1 l1 s2;
           canonical_sum_prod_ok r vm t1 s2 }
      aplus (amult (amult c1 (interp_vl r vm l1)) (interp_cs r vm s2))
            (amult (interp_cs r vm t1) (interp_cs r vm s2));
      == { distribute_right r (amult c1 (interp_vl r vm l1))
             (interp_cs r vm t1) (interp_cs r vm s2) }
      amult (aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm t1))
            (interp_cs r vm s2);
      == { }
      amult (interp_cs r vm s1) (interp_cs r vm s2);
    }
  | Cons_varlist l1 t1 ->
    calc (==) {
      interp_cs r vm (canonical_sum_prod r s1 s2);
      == { }
      interp_cs r vm
        (canonical_sum_merge r (canonical_sum_scalar2 r l1 s2)
                               (canonical_sum_prod r t1 s2));
      == { canonical_sum_merge_ok r vm
             (canonical_sum_scalar2 r l1 s2)
             (canonical_sum_prod r t1 s2) }
      aplus (interp_cs r vm (canonical_sum_scalar2 r l1 s2))
            (interp_cs r vm (canonical_sum_prod r t1 s2));
      == { canonical_sum_scalar2_ok r vm l1 s2;
           canonical_sum_prod_ok r vm t1 s2 }
      aplus (amult (interp_vl r vm l1) (interp_cs r vm s2))
            (amult (interp_cs r vm t1) (interp_cs r vm s2));
      == { distribute_right r (interp_vl r vm l1)
             (interp_cs r vm t1) (interp_cs r vm s2) }
      amult (aplus (interp_vl r vm l1) (interp_cs r vm t1))
            (interp_cs r vm s2);
      == { }
      amult (interp_cs r vm s1) (interp_cs r vm s2);
    }
  | Nil_monom -> ()

(*| Correctness of `FStar.Tactics.CanonCommSemiring.spolynomial_normalize`: the canonical sum has the same interpretation as the expression it was computed from. *)
val spolynomial_normalize_ok: #a:eqtype -> r:cr a -> vm:vmap a -> p:spolynomial a ->
  Lemma (interp_cs r vm (spolynomial_normalize r p) == interp_sp r vm p)
let rec spolynomial_normalize_ok #a r vm p =
  match p with
  | SPvar _ -> ()
  | SPconst _ -> ()
  | SPplus l q ->
    canonical_sum_merge_ok r vm
      (spolynomial_normalize r l) (spolynomial_normalize r q);
    spolynomial_normalize_ok r vm l;
    spolynomial_normalize_ok r vm q
  | SPmult l q ->
    canonical_sum_prod_ok r vm
      (spolynomial_normalize r l) (spolynomial_normalize r q);
    spolynomial_normalize_ok r vm l;
    spolynomial_normalize_ok r vm q

(*| Correctness of `FStar.Tactics.CanonCommSemiring.canonical_sum_simplify`: simplification preserves the interpretation of a canonical sum. *)
val canonical_sum_simplify_ok: #a:eqtype -> r:cr a -> vm:vmap a -> s:canonical_sum a ->
  Lemma (interp_cs r vm (canonical_sum_simplify r s) == interp_cs r vm s)
let rec canonical_sum_simplify_ok #a r vm s =
  let azero = r.cm_add.unit in
  let aone  = r.cm_mult.unit in
  match s with
  | Cons_monom c _ t -> canonical_sum_simplify_ok r vm t
  | Cons_varlist _ t -> canonical_sum_simplify_ok r vm t
  | Nil_monom -> ()

(*| Correctness of `FStar.Tactics.CanonCommSemiring.spolynomial_simplify`: the simplified canonical sum has the same interpretation as the expression it was computed from. *)
val spolynomial_simplify_ok: #a:eqtype -> r:cr a -> vm:vmap a -> p:spolynomial a ->
  Lemma (interp_cs r vm (spolynomial_simplify r p) == interp_sp r vm p)
let spolynomial_simplify_ok #a r vm p =
  canonical_sum_simplify_ok r vm (spolynomial_normalize r p);
  spolynomial_normalize_ok r vm p


(*| Reflected ring expressions, the form in which the tactic first reflects the sides of a goal.

    The constructors are `Pvar i` for the variable of index `i`, `Pconst c` for a constant of the carrier, `Pplus` and `Pmult` for addition and multiplication, and `Popp` for the additive inverse. `FStar.Tactics.CanonCommSemiring.interp_p` gives their meaning. *)
type polynomial a =
  | Pvar   : index -> polynomial a
  | Pconst : a -> polynomial a
  | Pplus  : polynomial a -> polynomial a -> polynomial a
  | Pmult  : polynomial a -> polynomial a -> polynomial a
  | Popp   : polynomial a -> polynomial a

(*| Computes the canonical sum of a reflected expression, before simplification; an additive inverse is computed as multiplication by `r.opp 1`.

    Its correctness is `FStar.Tactics.CanonCommSemiring.polynomial_normalize_ok`. *)
val polynomial_normalize: #a:eqtype -> cr a -> polynomial a -> canonical_sum a

[@@canon_attr]
let rec polynomial_normalize #a r p =
  match p with
  | Pvar i -> Cons_varlist (Cons_var i Nil_var) Nil_monom
  | Pconst c -> Cons_monom c Nil_var Nil_monom
  | Pplus l q ->
    canonical_sum_merge r (polynomial_normalize r l) (polynomial_normalize r q)
  | Pmult l q ->
    canonical_sum_prod r (polynomial_normalize r l) (polynomial_normalize r q)
  | Popp p ->
    canonical_sum_scalar3 r (r.opp r.cm_mult.unit) Nil_var (polynomial_normalize r p)

(*| Computes the simplified canonical sum of a reflected expression: `FStar.Tactics.CanonCommSemiring.polynomial_normalize` followed by `FStar.Tactics.CanonCommSemiring.canonical_sum_simplify`.

    This is the normal form compared by `FStar.Tactics.CanonCommSemiring.canon_semiring`; its correctness is `FStar.Tactics.CanonCommSemiring.polynomial_simplify_ok`. *)
val polynomial_simplify: #a:eqtype -> cr a -> polynomial a -> canonical_sum a

[@@canon_attr]
let polynomial_simplify #a r p =
  canonical_sum_simplify r
    (polynomial_normalize r p)

(*| Translates a reflected expression into one without additive inverses, replacing each `Popp p` by the product of the constant `r.opp 1` and the translation of `p`.

    Its correctness is `FStar.Tactics.CanonCommSemiring.spolynomial_of_ok`. *)
val spolynomial_of: #a:eqtype -> cr a -> polynomial a -> spolynomial a

[@@canon_attr]
let rec spolynomial_of #a r p =
  match p with
  | Pvar i -> SPvar i
  | Pconst c -> SPconst c
  | Pplus l q -> SPplus (spolynomial_of r l) (spolynomial_of r q)
  | Pmult l q -> SPmult (spolynomial_of r l) (spolynomial_of r q)
  | Popp p -> SPmult (SPconst (r.opp r.cm_mult.unit)) (spolynomial_of r p)

(*| Interprets a reflected expression, `FStar.Tactics.CanonCommSemiring.polynomial`, in a commutative ring, reading variables from the variable map. *)
[@@canon_attr]
let rec interp_p (#a:Type) (r:cr a) (vm:vmap a) (p:polynomial a) : a =
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match p with
  | Pconst c -> c
  | Pvar i -> interp_var vm i
  | Pplus p1 p2 -> aplus (interp_p r vm p1) (interp_p r vm p2)
  | Pmult p1 p2 -> amult (interp_p r vm p1) (interp_p r vm p2)
  | Popp p -> r.opp (interp_p r vm p)


(*| Correctness of `FStar.Tactics.CanonCommSemiring.spolynomial_of`: the translation without inverses has the same interpretation as the original expression. *)
val spolynomial_of_ok: #a:eqtype -> r:cr a -> vm:vmap a -> p:polynomial a ->
  Lemma (interp_p r vm p == interp_sp r vm (spolynomial_of r p))
let rec spolynomial_of_ok #a r vm p =
  match p with
  | Pconst c -> ()
  | Pvar i -> ()
  | Pplus p1 p2 ->
    spolynomial_of_ok r vm p1;
    spolynomial_of_ok r vm p2
  | Pmult p1 p2 ->
    spolynomial_of_ok r vm p1;
    spolynomial_of_ok r vm p2
  | Popp p ->
    spolynomial_of_ok r vm p;
    let x = interp_sp r vm (spolynomial_of r p) in
    let y = r.cm_mult.mult (r.opp r.cm_mult.unit) x in
    add_mult_opp r x;
    opp_unique r x y


(*| Normalizing a reflected expression directly with `FStar.Tactics.CanonCommSemiring.polynomial_normalize` gives a canonical sum with the same interpretation as normalizing its translation `FStar.Tactics.CanonCommSemiring.spolynomial_of` with `FStar.Tactics.CanonCommSemiring.spolynomial_normalize`. *)
val polynomial_normalize_ok: #a:eqtype -> r:cr a -> vm:vmap a -> p:polynomial a ->
  Lemma (interp_cs r vm (polynomial_normalize r p) ==
         interp_cs r vm (spolynomial_normalize r (spolynomial_of r p)))
let rec polynomial_normalize_ok #a r vm p =
  match p with
  | Pvar _ -> ()
  | Pconst _ -> ()
  | Pplus l q ->
    canonical_sum_merge_ok r vm
      (polynomial_normalize r l)
      (polynomial_normalize r q);
    canonical_sum_merge_ok r vm
      (spolynomial_normalize r (spolynomial_of r l))
      (spolynomial_normalize r (spolynomial_of r q));
    polynomial_normalize_ok r vm l;
    polynomial_normalize_ok r vm q

  | Pmult l q ->
    canonical_sum_prod_ok r vm
      (polynomial_normalize r l)
      (polynomial_normalize r q);
    canonical_sum_prod_ok r vm
      (spolynomial_normalize r (spolynomial_of r l))
      (spolynomial_normalize r (spolynomial_of r q));
    polynomial_normalize_ok r vm l;
    polynomial_normalize_ok r vm q

  | Popp p1 ->
    let l = SPconst (r.opp r.cm_mult.unit) in
    polynomial_normalize_ok r vm p1;
    canonical_sum_prod_ok r vm
      (spolynomial_normalize r l)
      (polynomial_normalize r p1);
    canonical_sum_prod_ok r vm
      (spolynomial_normalize r l)
      (spolynomial_normalize r (spolynomial_of r p1))


(*| Main correctness theorem of the semiring canonizer: the simplified canonical sum `FStar.Tactics.CanonCommSemiring.polynomial_simplify` has the same interpretation as the expression it was computed from.

    `FStar.Tactics.CanonCommSemiring.semiring_reflect` uses it to reduce an equation between ring expressions to an equation between canonical sums. *)
val polynomial_simplify_ok: #a:eqtype -> r:cr a -> vm:vmap a -> p:polynomial a ->
  Lemma (interp_cs r vm (polynomial_simplify r p) == interp_p r vm p)
let polynomial_simplify_ok #a r vm p =
  calc (==) {
    interp_cs r vm (polynomial_simplify r p);
    == { }
    interp_cs r vm (canonical_sum_simplify r (polynomial_normalize r p));
    == { canonical_sum_simplify_ok r vm (polynomial_normalize r p) }
    interp_cs r vm (polynomial_normalize r p);
    == { polynomial_normalize_ok r vm p }
    interp_cs r vm (spolynomial_normalize r (spolynomial_of r p));
    == { spolynomial_normalize_ok r vm (spolynomial_of r p) }
    interp_sp r vm (spolynomial_of r p);
    == { spolynomial_of_ok r vm p }
    interp_p r vm p;
  }


///
/// Tactic definition
///

(*| Dumps the proof state with the given message, but only when debugging is enabled. *)
let ddump m = if debugging () then dump m

(*| Returns the position of the first term of `xs` equal to `x` according to `FStar.Reflection.TermEq.Simple.term_eq`, counting from `n`, or `None` if there is none. *)
let rec find_aux (n:nat) (x:term) (xs:list term) : Tac (option nat) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq x x' then Some n else find_aux (n+1) x xs'

(*| Returns the position of the first term of a list equal to a given term according to `FStar.Reflection.TermEq.Simple.term_eq`, counting from `0`, or `None` if there is none. *)
let find = find_aux 0

(*| Reflects the term `t` as a variable: reuses the index of an equal term already in `ts`, or else allocates the next index, appends `t` to `ts` and binds the new variable to `unquotea t` in the variable map. *)
let make_fvar (#a:Type) (t:term) (unquotea:term -> Tac a) (ts:list term)
  (vm:vmap a) : Tac (polynomial a & list term & vmap a) =
  match find t ts with
  | Some v -> (Pvar v, ts, vm)
  | None ->
    let vfresh = length ts in
    let z = unquotea t in
    (Pvar vfresh, ts @ [t], update vfresh z vm)

(*| Reflects one term as a ring expression, extending the list of already seen opaque terms and the variable map.

    An application of a top-level name to two arguments becomes `Pplus` or `Pmult` when the head is equal to `add` or `mult`, an application to one argument becomes `Popp` when the head is equal to `opp`, and a literal constant becomes `Pconst`. Every other term becomes a variable through `FStar.Tactics.CanonCommSemiring.make_fvar`. Heads are compared with `FStar.Reflection.TermEq.Simple.term_eq`, so the operators and `t` are expected to be already normalized. The `mone` argument is currently unused. *)
let rec reification_aux (#a:Type) (unquotea:term -> Tac a) (ts:list term) (vm:vmap a) (add opp mone mult t: term) : Tac (polynomial a & list term & vmap a) =
  // ddump ("term = " ^ term_to_string t ^ "\n");
  let hd, tl = collect_app_ref t in
  match inspect hd, list_unref tl with
  | Tv_FVar fv, [(t1, _) ; (t2, _)] ->
    //ddump ("add = " ^ term_to_string add ^ "
    //     \nmul = " ^ term_to_string mult);
    //ddump ("fv = " ^ term_to_string (pack (Tv_FVar fv)));
    let binop (op:polynomial a -> polynomial a -> polynomial a) : Tac (polynomial a & list term & vmap a) =
      let (e1, ts, vm) = reification_aux unquotea ts vm add opp mone mult t1 in
      let (e2, ts, vm) = reification_aux unquotea ts vm add opp mone mult t2 in
      (op e1 e2, ts, vm)
      in
    if term_eq (pack (Tv_FVar fv)) add then binop Pplus else
    if term_eq (pack (Tv_FVar fv)) mult then binop Pmult else
    make_fvar t unquotea ts vm
  | Tv_FVar fv, [(t1, _)] ->
    let monop (op:polynomial a -> polynomial a) : Tac (polynomial a & list term & vmap a) =
      let (e, ts, vm) = reification_aux unquotea ts vm add opp mone mult t1 in
      (op e, ts, vm)
      in
    if term_eq (pack (Tv_FVar fv)) opp then monop Popp else
    make_fvar t unquotea ts vm
  | Tv_Const _, [] -> Pconst (unquotea t), ts, vm
  | _, _ -> make_fvar t unquotea ts vm

(*| The normalization steps used by the semiring tactic, chosen to unfold all that is needed and no more.

    They reduce primitive operations, matches and recursion, and unfold the definitions marked `FStar.Tactics.CanonCommSemiring.canon_attr`, the projections of `FStar.Algebra.CommMonoid.cm` and `FStar.Tactics.CanonCommSemiring.cr`, the integer monoids `FStar.Algebra.CommMonoid.int_plus_cm` and `FStar.Algebra.CommMonoid.int_multiply_cm`, `Prims.op_Star`, and the list and pair functions used by the interpretation. Definitions of a custom ring that should be unfolded need the `FStar.Tactics.CanonCommSemiring.canon_attr` attribute. *)
let steps =
  [
    primops;
    iota;
    zeta;
    delta_attr [`%canon_attr];
    delta_only [
      `%Prims.op_Star;                            // For integer ring
      `%FStar.Algebra.CommMonoid.int_plus_cm;     // For integer ring
      `%FStar.Algebra.CommMonoid.int_multiply_cm; // For integer ring
      `%FStar.Algebra.CommMonoid.CM?.mult;
      `%FStar.Algebra.CommMonoid.CM?.unit;
      `%CR?.cm_add;
      `%CR?.opp;
      `%CR?.cm_mult;
      `%FStar.List.Tot.assoc;
      `%FStar.Pervasives.Native.fst;
      `%FStar.Pervasives.Native.snd;
      `%FStar.Pervasives.Native.Mktuple2?._1;
      `%FStar.Pervasives.Native.Mktuple2?._2;
      `%FStar.List.Tot.op_At;
      `%FStar.List.Tot.append;
    ]
  ]

(*| Normalizes the current goal with `FStar.Tactics.CanonCommSemiring.steps`. *)
let canon_norm () : Tac unit = norm steps

(*| Reflects a list of terms as ring expressions over a shared variable map.

    The terms are first normalized with `FStar.Tactics.CanonCommSemiring.steps`, then each is reflected with `FStar.Tactics.CanonCommSemiring.reification_aux` using the already normalized operator terms `tadd`, `topp` and `tmult`. Equal subterms in different terms get the same variable. The variable map's default value is `munit`. *)
let reification (#a:Type)
  (unquotea:term -> Tac a) (quotea:a -> Tac term) (tadd topp tmone tmult:term) (munit:a) (ts:list term) : Tac (list (polynomial a) & vmap a) =
  // Be careful not to normalize operations too much
  // E.g. we don't want to turn ( +% ) into (a + b) % prime
  // or we won't be able to spot ring operations
  let add  = tadd in
  let opp  = topp in
  let mone = tmone in
  let mult = tmult in
  let ts = Tactics.Util.map (norm_term steps) ts in
  //ddump ("add = " ^ term_to_string add ^ "\nmult = " ^ term_to_string mult);
  let (es, _, vm) =
    Tactics.Util.fold_left
      (fun (es, vs, vm) t ->
        let (e, vs, vm) = reification_aux unquotea vs vm add opp mone mult t
        in (e::es, vs, vm))
      ([],[], ([], munit)) ts
  in (List.Tot.Base.rev es, vm)

(* The implicit argument in the application of `Pconst` is crucial *)
(*| Builds the syntax of a reflected ring expression, as a term of type `FStar.Tactics.CanonCommSemiring.polynomial` over the carrier whose syntax is `ta`. *)
let rec quote_polynomial (#a:Type) (ta:term) (quotea:a -> Tac term) (e:polynomial a) : Tac term =
  match e with
  | Pconst c -> mk_app (`Pconst) [(ta, Q_Implicit); (quotea c, Q_Explicit)]
  | Pvar x -> mk_e_app (`Pvar) [pack (Tv_Const (C_Int x (FStar.Sealed.seal Dec)))]
  | Pplus e1 e2 ->
    mk_e_app (`Pplus) [quote_polynomial ta quotea e1; quote_polynomial ta quotea e2]
  | Pmult e1 e2 ->
    mk_e_app (`Pmult) [quote_polynomial ta quotea e1; quote_polynomial ta quotea e2]
  | Popp e -> mk_e_app (`Popp) [quote_polynomial ta quotea e]

(*| The reflection lemma behind the semiring tactic: to prove `a1 == a2`, it suffices that `e1` and `e2` have equal simplified canonical sums and that `a1` and `a2` are the interpretations of `e1` and `e2`.

    Applying it creates three goals: the equality of the interpreted canonical sums and the two interpretation equations. Its proof uses `FStar.Tactics.CanonCommSemiring.polynomial_simplify_ok`. *)
let semiring_reflect (#a:eqtype) (r:cr a) (vm:vmap a) (e1 e2:polynomial a) (a1 a2:a)
    (_ : squash (
      interp_cs r vm (polynomial_simplify r e1) ==
      interp_cs r vm (polynomial_simplify r e2)))
    (_ : squash (a1 == interp_p r vm e1))
    (_ : squash (a2 == interp_p r vm e2)) :
    squash (a1 == a2)
  =
  polynomial_simplify_ok r vm e1;
  polynomial_simplify_ok r vm e2

(* [@@plugin] *)
(*| The implementation of the semiring tactic, working on explicit syntax of the carrier, the ring and its operations.

    It focuses on the current goal, which must be an equality, and fails with "Goal should be an equality" otherwise. It first restates the goal as an equality at type `ta`, solving the cut with `exact` or else with the SMT solver. It then reflects both sides with `FStar.Tactics.CanonCommSemiring.reification`, applies `FStar.Tactics.CanonCommSemiring.semiring_reflect`, closes the two interpretation goals by normalizing with `FStar.Tactics.CanonCommSemiring.steps` and `trefl`, and leaves the normalized equality of the two canonical forms as the remaining goal. Usually called through `FStar.Tactics.CanonCommSemiring.canon_semiring`. *)
let canon_semiring_aux
    (a: Type) (ta: term) (unquotea: term -> Tac a) (quotea: a -> Tac term)
    (tr tadd topp tmone tmult: term)
    (munit: a)
  : Tac unit
=
  focus (fun () ->
  norm []; // Do not normalize anything implicitly
  let g = cur_goal () in
  match term_as_formula g with
  | Comp (Eq (Some t)) t1 t2 ->
    (* First, make sure we have an equality at type ta, since otherwise
    we will fail to apply the reflection Lemma. We can just cut by the equality
    we want, since they should be equiprovable (though not equal). *)
    let b = tcut (`(squash (eq2 #(`#ta) (`#t1) (`#t2)))) in
    (* Try solving it trivially if type was exactly the same, or give to smt.
    It should really be trivial. *)
    begin
      try exact b with | _ -> smt ()
    end;
    begin
    match reification unquotea quotea tadd topp tmone tmult munit [t1; t2] with
    | ([e1; e2], vm) ->
(*
      ddump (term_to_string t1);
      ddump (term_to_string t2);
      let r : cr a = unquote tr in
      ddump ("vm = " ^ term_to_string (quote vm) ^ "\n" ^
             "before = " ^ term_to_string (norm_term steps
                  (quote (interp_p r vm e1 == interp_p r vm e2))));
      dump ("expected after = " ^ term_to_string (norm_term steps
        (quote (
            interp_cs r vm (polynomial_simplify r e1) ==
            interp_cs r vm (polynomial_simplify r e2)))));
*)
      let tvm = quote_vm ta quotea vm in
      let te1 = quote_polynomial ta quotea e1 in
      //ddump ("te1 = " ^ term_to_string te1);
      let te2 = quote_polynomial ta quotea e2 in
      //ddump ("te2 = " ^ term_to_string te2);
      mapply (`(semiring_reflect
        #(`#ta) (`#tr) (`#tvm) (`#te1) (`#te2) (`#t1) (`#t2)));
      //ddump "Before canonization";
      canon_norm ();
      //ddump "After canonization";
      later ();
      //ddump "Before normalizing left-hand side";
      canon_norm ();
      //ddump "After normalizing left-hand side";
      trefl ();
      //ddump "Before normalizing right-hand side";
      canon_norm ();
      //ddump "After normalizing right-hand side";
      trefl ()
    | _ -> fail "Unexpected"
    end
  | _ -> fail ("Goal should be an equality: " ^ term_to_string g))

(*| Proves or simplifies an equality goal in a commutative ring by bringing both sides to a canonical sum of monomials.

    The goal must be an equality at the carrier type of `r`. Additions, multiplications, applications of `r.opp` and literal constants are interpreted in `r`; every other subterm is treated as an opaque variable, so for example binary subtraction on `int` is not understood and should be written as addition of a negation. Coefficients of equal monomials are collected and trivial terms are removed, using `FStar.Tactics.CanonCommSemiring.polynomial_simplify`. The tactic replaces the goal by an equality between the two canonical forms, which is left open: it is typically syntactically trivial when the original sides are equal as polynomials, and is closed by SMT (at the end of an `assert ... by`) or by `trefl`. The integer instance is `FStar.Tactics.CanonCommSemiring.int_semiring`.

    ```fstar
    let ring_opp_example (x y : int) =
      assert ((x + - y) * (x + y) == x * x + - (y * y))
        by (FStar.Tactics.CanonCommSemiring.canon_semiring FStar.Tactics.CanonCommSemiring.int_cr)
    ``` *)
let canon_semiring (#a:eqtype) (r:cr a) : Tac unit =
  canon_semiring_aux a
    (quote a) (unquote #a) (fun (x:a) -> quote x) (quote r)
    (norm_term steps (quote r.cm_add.mult))
    (norm_term steps (quote r.opp))
    (norm_term steps (quote (r.opp r.cm_mult.unit)))
    (norm_term steps (quote r.cm_mult.mult))
    r.cm_add.unit

///  Ring of integers

(*| The commutative ring of mathematical integers, with `FStar.Algebra.CommMonoid.int_plus_cm`, `FStar.Algebra.CommMonoid.int_multiply_cm` and unary negation as additive inverse.

    Used by `FStar.Tactics.CanonCommSemiring.int_semiring`. *)
[@@canon_attr]
let int_cr : cr int =
  CR int_plus_cm int_multiply_cm op_Tilde_Minus (fun x -> ()) (fun x y z -> ()) (fun x -> ())

(*| Proves or simplifies an equality goal between `int` expressions by ring normalization: `FStar.Tactics.CanonCommSemiring.canon_semiring` applied to `FStar.Tactics.CanonCommSemiring.int_cr`.

    Addition, multiplication, unary negation and integer literals are understood; binary subtraction and other operations are treated as opaque. The remaining equality of canonical forms is left for SMT or `trefl`.

    ```fstar
    let ring_example (a b : int) =
      assert ((a + b) * (a + b) == a * a + 2 * a * b + b * b)
        by (FStar.Tactics.CanonCommSemiring.int_semiring ())
    ``` *)
let int_semiring () : Tac unit = canon_semiring int_cr
