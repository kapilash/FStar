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
module FStar.Tactics.CanonCommMonoidSimple.Equiv

open FStar.Algebra.CommMonoid.Equiv
open FStar.List
open FStar.Classical
open FStar.Tactics.CanonCommSwaps
open FStar.Tactics.V2.Bare

private
let term_eq = FStar.Reflection.TermEq.Simple.term_eq

(* A simple expression canonizer for commutative monoids (working up to
   some given equivalence relation as opposed to just propositional equality).
   For a canonizer with more features see FStar.Tactics.CanonCommMonoid.fst.

   Based on FStar.Tactics.CanonCommMonoidSimple.fst
*)

(* Only dump when debugging is on *)
//let dump m = if debugging () then dump m

(***** Expression syntax *)

// GM: ugh, we had `nat`, but then we get bitten by lack
//     of subtyping over datatypes when we typecheck the amap term
//     we generate (see convert_am).
(*| Atoms of a reified expression: variable indices standing for the opaque subterms of the goal.

    Each distinct subterm that is not a monoid operation or unit gets the next
    index, in order of first occurrence.
    It is `int` rather than `nat` so that the `amap` term built by
    `FStar.Tactics.CanonCommMonoidSimple.Equiv.convert_am` typechecks without subtyping on datatypes. *)
let atom : eqtype = int

(*| Syntax of commutative monoid expressions over `FStar.Tactics.CanonCommMonoidSimple.Equiv.atom`s.

    The constructors are `Unit` (the monoid unit), `Mult e1 e2` (the monoid
    operation) and `Atom x` (an opaque subterm). Their meaning is given by
    `FStar.Tactics.CanonCommMonoidSimple.Equiv.mdenote`. *)
type exp : Type =
  | Unit : exp
  | Mult : exp -> exp -> exp
  | Atom : atom -> exp

(*| Renders an `FStar.Tactics.CanonCommMonoidSimple.Equiv.exp` as a string such as `Mult (Atom 0) (Unit)`, for debugging. *)
let rec exp_to_string (e:exp) : string =
  match e with
  | Unit -> "Unit"
  | Atom x -> "Atom " ^ string_of_int (x <: atom)
  | Mult e1 e2 -> "Mult (" ^ exp_to_string e1
                   ^ ") (" ^ exp_to_string e2 ^ ")"

(***** Expression denotation *)

// Use a map that stores for each atom
// (1) its denotation that should be treated abstractly (type a) and
// (2) user-specified extra information depending on its term (type b)

(*| Maps atoms to their denotation in the carrier type `a`, with a default value.

    It is a pair of an association list and the default, returned by
    `FStar.Tactics.CanonCommMonoidSimple.Equiv.select` for unmapped atoms. Build one with `FStar.Tactics.CanonCommMonoidSimple.Equiv.const` and
    `FStar.Tactics.CanonCommMonoidSimple.Equiv.update`. *)
let amap (a:Type) = list (atom & a) & a
(*| The atom map that sends every atom to `xa`. *)
let const (#a:Type) (xa:a) : amap a = ([], xa)
(*| Looks up the denotation of an atom in an `FStar.Tactics.CanonCommMonoidSimple.Equiv.amap`, returning the default value when it is not mapped.

    The most recently added binding of an atom wins. *)
let select (#a:Type) (x:atom) (am:amap a) : Tot a =
  match assoc #atom #a x (fst am) with
  | Some a -> a
  | _ -> snd am
(*| Maps atom `x` to `xa` in an `FStar.Tactics.CanonCommMonoidSimple.Equiv.amap`, shadowing any earlier binding of `x`. *)
let update (#a:Type) (x:atom) (xa:a) (am:amap a) : amap a =
  (x, xa)::fst am, snd am

(*| Interprets an `FStar.Tactics.CanonCommMonoidSimple.Equiv.exp` in the commutative monoid `m`, reading atoms in `am`.

    `Unit` denotes `CM?.unit m` and `Mult` denotes `CM?.mult m`. *)
let rec mdenote (#a:Type u#aa) (eq:equiv a) (m:cm a eq) (am:amap a) (e:exp) : a =
  match e with
  | Unit -> CM?.unit m
  | Atom x -> select x am
  | Mult e1 e2 -> CM?.mult m (mdenote eq m am e1) (mdenote eq m am e2)

(*| Interprets a list of atoms as their product in `m`, associated to the right.

    The empty list denotes the unit, and a singleton denotes its atom without a
    trailing unit. *)
let rec xsdenote (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (xs:list atom) : a =
  match xs with
  | [] -> CM?.unit m
  | [x] -> select x am
  | x::xs' -> CM?.mult m (select x am) (xsdenote eq m am xs')

(***** Flattening expressions to lists of atoms *)

(*| Lists the atoms of an expression from left to right, dropping units. *)
let rec flatten (e:exp) : list atom =
  match e with
  | Unit -> []
  | Atom x -> [x]
  | Mult e1 e2 -> flatten e1 @ flatten e2

(*| `FStar.Tactics.CanonCommMonoidSimple.Equiv.xsdenote` of a concatenation is `EQ?.eq eq`-equivalent (the monoid's equivalence relation) to the product of the denotations of the two parts. *)
let rec flatten_correct_aux (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (xs1 xs2:list atom)
  : Lemma (xsdenote eq m am (xs1 @ xs2) `EQ?.eq eq` CM?.mult m (xsdenote eq m am xs1)
                                                               (xsdenote eq m am xs2)) =
  match xs1 with
  | [] ->
      CM?.identity m (xsdenote eq m am xs2);
      EQ?.symmetry eq (CM?.mult m (CM?.unit m) (xsdenote eq m am xs2)) (xsdenote eq m am xs2)
  | [x] -> (
      if (Nil? xs2)
      then (right_identity eq m (select x am);
            EQ?.symmetry eq (CM?.mult m (select x am) (CM?.unit m)) (select x am))
      else EQ?.reflexivity eq (CM?.mult m (xsdenote eq m am [x]) (xsdenote eq m am xs2)))
  | x::xs1' ->
      flatten_correct_aux eq m am xs1' xs2;
      EQ?.reflexivity eq (select x am);
      CM?.congruence m (select x am) (xsdenote eq m am (xs1' @ xs2))
                       (select x am) (CM?.mult m (xsdenote eq m am xs1') (xsdenote eq m am xs2));
      CM?.associativity m (select x am) (xsdenote eq m am xs1') (xsdenote eq m am xs2);
      EQ?.symmetry eq (CM?.mult m (CM?.mult m (select x am) (xsdenote eq m am xs1')) (xsdenote eq m am xs2))
                      (CM?.mult m (select x am) (CM?.mult m (xsdenote eq m am xs1') (xsdenote eq m am xs2)));
      EQ?.transitivity eq (CM?.mult m (select x am) (xsdenote eq m am (xs1' @ xs2)))
                          (CM?.mult m (select x am) (CM?.mult m (xsdenote eq m am xs1') (xsdenote eq m am xs2)))
                          (CM?.mult m (CM?.mult m (select x am) (xsdenote eq m am xs1')) (xsdenote eq m am xs2))

(*| An expression and the list of its atoms, as given by `FStar.Tactics.CanonCommMonoidSimple.Equiv.flatten`, have `EQ?.eq eq`-equivalent (the monoid's equivalence relation) denotations. *)
let rec flatten_correct (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (e:exp)
  : Lemma (mdenote eq m am e `EQ?.eq eq` xsdenote eq m am (flatten e)) =
  match e with
  | Unit -> EQ?.reflexivity eq (CM?.unit m)
  | Atom x -> EQ?.reflexivity eq (select x am)
  | Mult e1 e2 ->
      flatten_correct_aux eq m am (flatten e1) (flatten e2);
      EQ?.symmetry eq (xsdenote eq m am (flatten e1 @ flatten e2))
                      (CM?.mult m (xsdenote eq m am (flatten e1)) (xsdenote eq m am (flatten e2)));
      flatten_correct eq m am e1;
      flatten_correct eq m am e2;
      CM?.congruence m (mdenote eq m am e1) (mdenote eq m am e2)
                       (xsdenote eq m am (flatten e1)) (xsdenote eq m am (flatten e2));
      EQ?.transitivity eq (CM?.mult m (mdenote eq m am e1) (mdenote eq m am e2))
                          (CM?.mult m (xsdenote eq m am (flatten e1)) (xsdenote eq m am (flatten e2)))
                          (xsdenote eq m am (flatten e1 @ flatten e2))

(***** Permuting the lists of atoms
       by swapping adjacent elements *)

(*| The type of functions that reorder lists of atoms, such as `FStar.Tactics.CanonCommMonoidSimple.Equiv.sort`. *)
let permute = list atom -> list atom

// high-level correctness criterion for permutations
(*| States that a permutation function `p` preserves `FStar.Tactics.CanonCommMonoidSimple.Equiv.xsdenote` (up to `EQ?.eq eq`) in every commutative monoid and atom map.

    This is the correctness criterion for the reordering step of the
    canonizer; `FStar.Tactics.CanonCommMonoidSimple.Equiv.permute_via_swaps_correct` establishes it. *)
let permute_correct (p:permute) =
  #a:Type -> eq:equiv a -> m:cm a eq -> am:amap a -> xs:list atom ->
    Lemma (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (p xs))

// sufficient condition:
// permutation has to be expressible as swaps of adjacent list elements

// In the general case, an arbitrary permutation can be done via swaps.
// (see FStar.Tactics.CanonCommSwaps for a proof)

(*| Applying one adjacent swap (at an offset, as in `FStar.Tactics.CanonCommSwaps.apply_swap_aux`) gives a list of atoms with `EQ?.eq eq`-equivalent (the monoid's equivalence relation) denotation.

    This is where commutativity and associativity of the monoid are used. *)
let rec apply_swap_aux_correct (#a:Type) (n:nat) (eq:equiv a) (m:cm a eq) (am:amap a)
                           (xs:list atom) (s:swap (length xs + n))
  : Lemma (requires True)
      (ensures (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (apply_swap_aux n xs s)))
      (decreases xs) =
  match xs with
  | [] -> EQ?.reflexivity eq (CM?.unit m)
  | [x] -> EQ?.reflexivity eq (select x am)
  | [x1;x2] ->
      if n = (s <: nat)
      then CM?.commutativity m (select x1 am) (select x2 am)
      else EQ?.reflexivity eq (xsdenote eq m am [x1;x2])
  | x1 :: x2 :: xs' ->
      if n = (s <: nat)
      then (
        CM?.associativity m (select x1 am) (select x2 am) (xsdenote eq m am xs');
        EQ?.symmetry eq (CM?.mult m (CM?.mult m (select x1 am) (select x2 am)) (xsdenote eq m am xs'))
                        (CM?.mult m (select x1 am) (CM?.mult m (select x2 am) (xsdenote eq m am xs')));
        CM?.commutativity m (select x1 am) (select x2 am);
        EQ?.reflexivity eq (xsdenote eq m am xs');
        CM?.congruence m (CM?.mult m (select x1 am) (select x2 am)) (xsdenote eq m am xs')
                         (CM?.mult m (select x2 am) (select x1 am)) (xsdenote eq m am xs');
        CM?.associativity m (select x2 am) (select x1 am) (xsdenote eq m am xs');
        EQ?.transitivity eq (CM?.mult m (select x1 am) (CM?.mult m (select x2 am) (xsdenote eq m am xs')))
                            (CM?.mult m (CM?.mult m (select x1 am) (select x2 am)) (xsdenote eq m am xs'))
                            (CM?.mult m (CM?.mult m (select x2 am) (select x1 am)) (xsdenote eq m am xs'));
        EQ?.transitivity eq (CM?.mult m (select x1 am) (CM?.mult m (select x2 am) (xsdenote eq m am xs')))
                            (CM?.mult m (CM?.mult m (select x2 am) (select x1 am)) (xsdenote eq m am xs'))
                            (CM?.mult m (select x2 am) (CM?.mult m (select x1 am) (xsdenote eq m am xs'))))
      else (
        apply_swap_aux_correct (n+1) eq m am (x2 :: xs') s;
        EQ?.reflexivity eq (select x1 am);
        CM?.congruence m (select x1 am) (xsdenote eq m am (x2 :: xs'))
                         (select x1 am) (xsdenote eq m am (apply_swap_aux (n+1) (x2 :: xs') s)))

(*| Applying one adjacent swap with `FStar.Tactics.CanonCommSwaps.apply_swap` gives a list of atoms with `EQ?.eq eq`-equivalent (the monoid's equivalence relation) denotation. *)
let apply_swap_correct (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a)
                       (xs:list atom) (s:swap (length xs))
  : Lemma (ensures (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (apply_swap xs s)))
          (decreases xs) =
  apply_swap_aux_correct 0 eq m am xs s

(*| Applying a list of adjacent swaps with `FStar.Tactics.CanonCommSwaps.apply_swaps` gives a list of atoms with `EQ?.eq eq`-equivalent (the monoid's equivalence relation) denotation. *)
let rec apply_swaps_correct (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a)
                            (xs:list atom) (ss:list (swap (length xs)))
  : Lemma (requires True)
      (ensures (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (apply_swaps xs ss)))
      (decreases ss) =
  match ss with
  | [] -> EQ?.reflexivity eq (xsdenote eq m am xs)
  | s::ss' ->
      apply_swap_correct eq m am xs s;
      apply_swaps_correct eq m am (apply_swap xs s) ss';
      EQ?.transitivity eq (xsdenote eq m am xs)
                          (xsdenote eq m am (apply_swap xs s))
                          (xsdenote eq m am (apply_swaps (apply_swap xs s) ss'))

(*| States that, for every list of atoms `xs`, `p xs` can be obtained from `xs` by a sequence of adjacent swaps.

    A sufficient condition for `FStar.Tactics.CanonCommMonoidSimple.Equiv.permute_correct`, see
    `FStar.Tactics.CanonCommMonoidSimple.Equiv.permute_via_swaps_correct`. *)
let permute_via_swaps (p:permute) =
  (#a:Type) -> (am:amap a) -> xs:list atom ->
    Lemma (exists (ss:swaps_for xs). p xs == apply_swaps xs ss)

(*| A permutation that can be realized by adjacent swaps preserves the denotation of every list of atoms (up to `EQ?.eq eq`). *)
let permute_via_swaps_correct_aux (p:permute) (pvs:permute_via_swaps p)
                               (#a:Type) (eq:equiv a)(m:cm a eq) (am:amap a) (xs:list atom)
  : Lemma (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (p xs)) =
  pvs am xs;
  assert(exists (ss:swaps_for xs). p xs == apply_swaps xs ss);
  exists_elim (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (p xs))
    (() <: squash (exists (ss:swaps_for xs). p xs == apply_swaps xs ss))
    (fun ss -> apply_swaps_correct eq m am xs ss)

(*| Every permutation that can be realized by adjacent swaps (`FStar.Tactics.CanonCommMonoidSimple.Equiv.permute_via_swaps`) is correct in the sense of `FStar.Tactics.CanonCommMonoidSimple.Equiv.permute_correct`. *)
let permute_via_swaps_correct
  (p:permute) (pvs:permute_via_swaps p) : permute_correct p =
     fun #a -> permute_via_swaps_correct_aux p pvs #a

(***** Sorting atoms is a correct permutation
       (since it can be done by swaps) *)

// Here we sort the variable numbers

(*| Sorts a list of atoms in increasing order of index, with `FStar.List.Tot.Base.sortWith`.

    This is the reordering used by `FStar.Tactics.CanonCommMonoidSimple.Equiv.canon`. *)
let sort : permute = List.Tot.Base.sortWith #int (compare_of_bool (<))

(*| Sorting a list of atoms can be realized by adjacent swaps.

    Proved with `FStar.Tactics.CanonCommSwaps.equal_counts_implies_swaps`, since
    `FStar.List.Tot.Base.sortWith` preserves element counts. *)
let sort_via_swaps (#a:Type) (am:amap a)  (xs:list atom)
  : Lemma (exists (ss:swaps_for xs). sort xs == apply_swaps xs ss) 
  = List.Tot.Properties.sortWith_permutation #int (compare_of_bool (<)) xs;
    let ss = equal_counts_implies_swaps xs (sort xs) in
    ()

(*| Sorting a list of atoms with `FStar.Tactics.CanonCommMonoidSimple.Equiv.sort` preserves its denotation (up to `EQ?.eq eq`). *)
let sort_correct_aux (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (xs:list atom)
  : Lemma (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (sort xs)) =
  permute_via_swaps_correct sort (fun #a am -> sort_via_swaps am) eq m am xs

(*| `FStar.Tactics.CanonCommMonoidSimple.Equiv.sort` is a correct permutation in the sense of `FStar.Tactics.CanonCommMonoidSimple.Equiv.permute_correct`. *)
let sort_correct : permute_correct sort = (fun #a -> sort_correct_aux #a)

(***** Canonicalization tactics *)

(*| Computes the canonical form of an expression: its atoms, units dropped, sorted by index.

    Two expressions that are equal by associativity, commutativity and the
    unit laws have the same canonical form. *)
let canon (e:exp) = sort (flatten e)

(*| An expression and its canonical form `FStar.Tactics.CanonCommMonoidSimple.Equiv.canon e` have `EQ?.eq eq`-equivalent (the monoid's equivalence relation) denotations. *)
let canon_correct (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (e:exp)
  : Lemma (mdenote eq m am e `EQ?.eq eq` xsdenote eq m am (canon e)) =
  flatten_correct eq m am e;
  sort_correct eq m am (flatten e);
  EQ?.transitivity eq (mdenote eq m am e)
                      (xsdenote eq m am (flatten e))
                      (xsdenote eq m am (sort (flatten e)))

(*| Two expressions have `EQ?.eq eq`-equivalent (the monoid's equivalence relation) denotations when their canonical forms do.

    The `Lemma` form of `FStar.Tactics.CanonCommMonoidSimple.Equiv.monoid_reflect`. *)
let monoid_reflect_orig (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (e1 e2:exp)
  : Lemma (requires (xsdenote eq m am (canon e1) `EQ?.eq eq` xsdenote eq m am (canon e2)))
          (ensures (mdenote eq m am e1 `EQ?.eq eq` mdenote eq m am e2)) =
  canon_correct eq m am e1;
  canon_correct eq m am e2;
  EQ?.symmetry eq (mdenote eq m am e2) (xsdenote eq m am (canon e2));
  EQ?.transitivity eq (mdenote eq m am e1)
                      (xsdenote eq m am (canon e1))
                      (xsdenote eq m am (canon e2));
  EQ?.transitivity eq (mdenote eq m am e1)
                      (xsdenote eq m am (canon e2))
                      (mdenote eq m am e2)

(*| Reduces an `EQ?.eq eq` goal between two expression denotations to the same relation between the denotations of their canonical forms.

    Stated with a `squash` argument and result so that
    `FStar.Tactics.CanonCommMonoidSimple.Equiv.canon_monoid` can `apply` it to the goal. *)
let monoid_reflect (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (e1 e2:exp)
    (_ : squash (xsdenote eq m am (canon e1) `EQ?.eq eq` xsdenote eq m am (canon e2)))
       : squash (mdenote eq m am e1 `EQ?.eq eq` mdenote eq m am e2) =
  monoid_reflect_orig #a eq m am e1 e2

(* Finds the position of first occurrence of x in xs.
   This is now specialized to terms and their funny term_eq. *)
(*| Returns `Some (n + i)` where `i` is the position of the first term of `xs` that is syntactically equal to `x`, or `None` if there is none.

    Syntactic equality is `FStar.Reflection.TermEq.Simple.term_eq`. *)
let rec where_aux (n:nat) (x:term) (xs:list term) :
    Tac (option nat) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq x x' then Some n else where_aux (n+1) x xs'
(*| Returns the position of the first term in a list that is syntactically equal to `x`, or `None`.

    Defined as `FStar.Tactics.CanonCommMonoidSimple.Equiv.where_aux 0`; used during reification to reuse the atom
    index of a subterm already seen. *)
let where = where_aux 0

(*| Returns the atom for a term, allocating a fresh one when the term is not yet in `ts`.

    A term already in `ts` (up to `FStar.Reflection.TermEq.Simple.term_eq`)
    reuses its index. Otherwise the term is normalized with `iota` and `zeta`,
    gets index `length ts`, is appended to `ts`, and is recorded in the atom
    map, which maps atoms to terms. *)
let fatom (t:term) (ts:list term) (am:amap term) : Tac (exp & list term & amap term) =
  match where t ts with
  | Some v -> (Atom v, ts, am)
  | None ->
    let vfresh = length ts in
    let t = norm_term [iota; zeta] t in
    (Atom vfresh, ts @ [t], update vfresh t am)

// This expects that mult, unit, and t have already been normalized
(*| Reifies a term into an `FStar.Tactics.CanonCommMonoidSimple.Equiv.exp`, extending the list of known atom terms `ts` and the term-valued atom map `am`.

    An application of an fvar that is syntactically equal to `mult` to two
    explicit arguments becomes `Mult`, and a term equal to `unit` becomes
    `Unit`. Any other term becomes an atom through `FStar.Tactics.CanonCommMonoidSimple.Equiv.fatom`. Expects `mult`,
    `unit` and `t` to be normalized already, as done by `FStar.Tactics.CanonCommMonoidSimple.Equiv.reification`. *)
let rec reification_aux (ts:list term) (am:amap term)
                        (mult unit t : term) : Tac (exp & list term & amap term) =
  let hd, tl = collect_app t in
  match inspect hd, tl with
  | Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)] ->
    if term_eq (pack (Tv_FVar fv)) mult
    then (let (e1, ts, am) = reification_aux ts am mult unit t1 in
          let (e2, ts, am) = reification_aux ts am mult unit t2 in
          (Mult e1 e2, ts, am))
    else fatom t ts am
  | _, _ ->
    if term_eq t unit
    then (Unit, ts, am)
    else fatom t ts am

(*| Reifies a term into an `FStar.Tactics.CanonCommMonoidSimple.Equiv.exp` for the monoid given by the quoted term `m`, returning the expression with the updated atom list and atom map.

    Normalizes `CM?.mult m` and `CM?.unit m` with `iota`, `zeta` and `delta`,
    and the term with `iota` and `zeta` only, then calls
    `FStar.Tactics.CanonCommMonoidSimple.Equiv.reification_aux`. The argument `eq` is not used. *)
let reification (eq: term) (m: term) (ts:list term) (am:amap term) (t:term) :
    Tac (exp & list term & amap term) =
  let mult = norm_term [iota; zeta; delta] (`CM?.mult (`#m)) in
  let unit = norm_term [iota; zeta; delta] (`CM?.unit (`#m)) in
  let t    = norm_term [iota; zeta] t in
  reification_aux ts am mult unit t

(*| Tactic that tries to close the current goal with `FStar.Algebra.CommMonoid.Equiv.right_identity`, and otherwise with `CM?.congruence m`, reflexivity of `eq` on the first factor, and a recursive call on the second.

    It handles goals relating two right-nested products that agree up to a
    trailing unit. It fails when neither step applies. Used by
    `FStar.Tactics.CanonCommMonoidSimple.Equiv.canon_lhs_rhs` when reflexivity alone does not close the goal. *)
let rec repeat_cong_right_identity (eq: term) (m: term) : Tac unit =
  or_else (fun _ -> apply_lemma (`right_identity))
          (fun _ -> apply_lemma (`CM?.congruence (`#m));
                    split ();
                    apply_lemma (`EQ?.reflexivity (`#eq));
                    repeat_cong_right_identity eq m
                    )

(*| Builds the term of an association list from atoms to terms, with the atoms quoted as integer literals.

    Helper for `FStar.Tactics.CanonCommMonoidSimple.Equiv.convert_am`. *)
let rec convert_map (m : list (atom & term)) : term =
  match m with
  | [] -> `[]
  | (a, t)::ps ->
      let a = pack (Tv_Const (C_Int a (FStar.Sealed.seal Dec))) in
      (* let t = norm_term [delta] t in *)
      `((`#a, (`#t)) :: (`#(convert_map ps)))

(* `am` is an amap (basically a list) of terms, each representing a value
of type `a` (whichever we are canonicalizing). This functions converts
`am` into a single `term` of type `amap a`, suitable to call `mdenote` with *)
(*| Builds a single term of type `amap a` from an atom map whose values are terms of type `a`.

    The result can be passed to `FStar.Tactics.CanonCommMonoidSimple.Equiv.mdenote` in a goal. *)
let convert_am (am : amap term) : term =
  let (map, def) = am in
  (* let def = norm_term [delta] def in *)
  `( (`#(convert_map map), `#def) )

(*| Builds the term that denotes an `FStar.Tactics.CanonCommMonoidSimple.Equiv.exp` value, quoting atom indices as integer literals. *)
let rec quote_exp (e:exp) : term =
    match e with
    | Unit -> (`Unit)
    | Mult e1 e2 -> (`Mult (`#(quote_exp e1)) (`#(quote_exp e2)))
    | Atom n -> let nt = pack (Tv_Const (C_Int n (FStar.Sealed.seal Dec))) in
                (`Atom (`#nt))

(*| Tactic that proves the current goal, which relates `lhs` and `rhs` by `EQ?.eq eq` for the quoted equivalence `eq` and monoid `m`, by canonicalizing both sides.

    Both sides are reified with shared atoms, the goal is changed to an
    `EQ?.eq eq` relation between `FStar.Tactics.CanonCommMonoidSimple.Equiv.mdenote` terms, `FStar.Tactics.CanonCommMonoidSimple.Equiv.monoid_reflect` is
    applied, and the result is normalized. The goal is then closed with
    `EQ?.reflexivity eq` or, failing that, with
    `FStar.Tactics.CanonCommMonoidSimple.Equiv.repeat_cong_right_identity`; the tactic fails if neither succeeds. *)
let canon_lhs_rhs (eq: term) (m: term) (lhs rhs:term) : Tac unit =
  let m_unit = norm_term [iota; zeta; delta](`CM?.unit (`#m)) in
  let am = const m_unit in (* empty map *)
  let (r1, ts, am) = reification eq m [] am lhs in
  let (r2,  _, am) = reification eq m ts am rhs in
  //dump ("am = " ^ term_to_string (quote am));
  //dump ("r1 = " ^ term_to_string (norm_term [delta;primops] (quote (mdenote eq m am r1))));
  //dump ("r2 = " ^ term_to_string (norm_term [delta;primops] (quote (mdenote eq m am r2))));
  //dump ("before = " ^ term_to_string (norm_term [hnf;delta;primops]
  //   (quote (mdenote eq m am r1 `EQ?.eq eq` mdenote eq m am r2))));
  //dump ("current goal -- " ^ term_to_string (cur_goal ()));
  let am = convert_am am in
  let r1 = quote_exp r1 in
  let r2 = quote_exp r2 in
  change_sq (`(mdenote (`#eq) (`#m) (`#am) (`#r1)
                 `EQ?.eq (`#eq)`
               mdenote (`#eq) (`#m) (`#am) (`#r2)));
  (* dump ("expected after = " ^ term_to_string (norm_term [delta;primops] *)
  (*    (quote (xsdenote eq m am (canon r1) `EQ?.eq eq` *)
  (*            xsdenote eq m am (canon r2))))); *)
  apply (`monoid_reflect);
  //dump ("after apply monoid_reflect");
  norm [iota; zeta; delta_only [`%canon; `%xsdenote; `%flatten; `%sort;
                    `%select; `%assoc; `%fst; `%Mktuple2?._1;
                    `%(@); `%append; `%List.Tot.sortWith;
                    `%List.Tot.partition; `%bool_of_compare;
                    `%compare_of_bool;
       ]; primops];
  //dump "before refl";
  or_else (fun _ -> apply_lemma (`(EQ?.reflexivity (`#eq))))
          (fun _ -> repeat_cong_right_identity eq m)

(*| Tactic that proves that two terms are related by `EQ?.eq eq` in a commutative monoid, by canonicalizing both sides modulo associativity, commutativity and unit laws.

    The equivalence `eq` and the monoid `m` are passed as quoted terms. After
    normalizing with `iota` and `zeta`, the goal must be `squash` applied to a
    relation whose last two arguments are explicit; they are taken as `lhs`
    and `rhs` and handed to `FStar.Tactics.CanonCommMonoidSimple.Equiv.canon_lhs_rhs`. The tactic fails with an
    error message when the goal does not have this shape. Unlike
    `FStar.Tactics.CanonCommMonoidSimple.canon_monoid`, it closes the goal
    itself.

    ```fstar
    let comm_plus_equiv (a b c: int) =
      assert (a + (b + 0) + c == c + (b + a))
        by (CME.canon_monoid (`FStar.Algebra.CommMonoid.Equiv.equality_equiv int)
                             (`FStar.Algebra.CommMonoid.Equiv.int_plus_cm))
    ``` *)
[@@plugin]
let canon_monoid (eq: term) (m: term) : Tac unit =
  norm [iota; zeta];
  let t = cur_goal () in
  // removing top-level squash application
  let sq, rel_xy = collect_app t in
  // unpacking the application of the equivalence relation (lhs `EQ?.eq eq` rhs)
  (match rel_xy with
   | [(rel_xy,_)] -> (
       let rel, xy = collect_app rel_xy in
       if (length xy >= 2)
       then (
         match FStar.List.Tot.Base.index xy (length xy - 2) , FStar.List.Tot.index xy (length xy - 1) with
         | (lhs, Q_Explicit) , (rhs, Q_Explicit) -> canon_lhs_rhs eq m lhs rhs
         | _ -> fail "Goal should have been an application of a binary relation to 2 explicit arguments"
       )
       else (
         fail "Goal should have been an application of a binary relation to n implicit and 2 explicit arguments"
       )
     )
   | _ -> fail "Goal should be squash applied to a binary relation")
