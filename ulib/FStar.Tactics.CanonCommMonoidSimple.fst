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
module FStar.Tactics.CanonCommMonoidSimple

open FStar.Algebra.CommMonoid
open FStar.List
open FStar.Reflection.V2
open FStar.Tactics.V2.Bare
open FStar.Classical
open FStar.Tactics.CanonCommSwaps

(*| Syntactic equality of terms, an alias for `FStar.Reflection.TermEq.Simple.term_eq`.

    Used to recognize the monoid operation and unit and to share atoms. *)
let term_eq = FStar.Reflection.TermEq.Simple.term_eq

(* A simple expression canonizer for commutative monoids.
   For a canonizer with more features see FStar.Tactics.CanonCommMonoid.fst.

   Inspired by:
   - http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html
   - http://poleiro.info/posts/2015-04-13-writing-reflective-tactics.html
*)

(* Only dump when debugging is on *)
(*| Prints the proof state with a message, like `FStar.Stubs.Tactics.V2.Builtins.dump`, but only when debugging is enabled.

    Debugging is tested with `FStar.Stubs.Tactics.V2.Builtins.debugging`. *)
let dump m = if debugging () then dump m

(***** Expression syntax *)

(*| Atoms of a reified expression: variable indices standing for the opaque subterms of the goal.

    Each distinct subterm that is not a monoid operation or unit gets the next
    index, in order of first occurrence. *)
let atom : eqtype = nat

(*| Syntax of commutative monoid expressions over `FStar.Tactics.CanonCommMonoidSimple.atom`s.

    The constructors are `Unit` (the monoid unit), `Mult e1 e2` (the monoid
    operation) and `Atom x` (an opaque subterm). Their meaning is given by
    `FStar.Tactics.CanonCommMonoidSimple.mdenote`. *)
type exp : Type =
  | Unit : exp
  | Mult : exp -> exp -> exp
  | Atom : atom -> exp

(*| Renders an `FStar.Tactics.CanonCommMonoidSimple.exp` as a string such as `Mult (Atom 0) (Unit)`, for debugging. *)
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
    `FStar.Tactics.CanonCommMonoidSimple.select` for unmapped atoms. Build one with `FStar.Tactics.CanonCommMonoidSimple.const` and
    `FStar.Tactics.CanonCommMonoidSimple.update`. *)
let amap (a:Type) = list (atom & a) & a
(*| The atom map that sends every atom to `xa`. *)
let const (#a:Type) (xa:a) : amap a = ([], xa)
(*| Looks up the denotation of an atom in an `FStar.Tactics.CanonCommMonoidSimple.amap`, returning the default value when it is not mapped.

    The most recently added binding of an atom wins. *)
let select (#a:Type) (x:atom) (am:amap a) : Tot a =
  match assoc #atom #a x (fst am) with
  | Some a -> a
  | _ -> snd am
(*| Maps atom `x` to `xa` in an `FStar.Tactics.CanonCommMonoidSimple.amap`, shadowing any earlier binding of `x`. *)
let update (#a:Type) (x:atom) (xa:a) (am:amap a) : amap a =
  (x, xa)::fst am, snd am

(*| Interprets an `FStar.Tactics.CanonCommMonoidSimple.exp` in the commutative monoid `m`, reading atoms in `am`.

    `Unit` denotes `CM?.unit m` and `Mult` denotes `CM?.mult m`. *)
let rec mdenote (#a:Type) (m:cm a) (am:amap a) (e:exp) : a =
  match e with
  | Unit -> CM?.unit m
  | Atom x -> select x am
  | Mult e1 e2 -> CM?.mult m (mdenote m am e1) (mdenote m am e2)

(*| Interprets a list of atoms as their product in `m`, associated to the right.

    The empty list denotes the unit, and a singleton denotes its atom without a
    trailing unit. *)
let rec xsdenote (#a:Type) (m:cm a) (am:amap a) (xs:list atom) : a =
  match xs with
  | [] -> CM?.unit m
  | [x] -> select x am
  | x::xs' -> CM?.mult m (select x am) (xsdenote m am xs')

(***** Flattening expressions to lists of atoms *)

(*| Lists the atoms of an expression from left to right, dropping units. *)
let rec flatten (e:exp) : list atom =
  match e with
  | Unit -> []
  | Atom x -> [x]
  | Mult e1 e2 -> flatten e1 @ flatten e2

(*| `FStar.Tactics.CanonCommMonoidSimple.xsdenote` of a concatenation is equal to the product of the denotations of the two parts. *)
let rec flatten_correct_aux (#a:Type) (m:cm a) (am:amap a) (xs1 xs2:list atom) :
    Lemma (xsdenote m am (xs1 @ xs2) == CM?.mult m (xsdenote m am xs1)
                                                   (xsdenote m am xs2)) =
  match xs1 with
  | [] -> CM?.identity m (xsdenote m am xs2)
  | [x] -> if (Nil? xs2) then right_identity m (select x am)
  | x::xs1' -> (CM?.associativity m (select x am)
                      (xsdenote m am xs1') (xsdenote m am xs2);
                flatten_correct_aux m am xs1' xs2)

(*| An expression and the list of its atoms, as given by `FStar.Tactics.CanonCommMonoidSimple.flatten`, have equal denotations. *)
let rec flatten_correct (#a:Type) (m:cm a) (am:amap a) (e:exp) :
    Lemma (mdenote m am e == xsdenote m am (flatten e)) =
  match e with
  | Unit | Atom _ -> ()
  | Mult e1 e2 -> flatten_correct_aux m am (flatten e1) (flatten e2);
                  flatten_correct m am e1; flatten_correct m am e2

(***** Permuting the lists of atoms
       by swapping adjacent elements *)

(*| The type of functions that reorder lists of atoms, such as `FStar.Tactics.CanonCommMonoidSimple.sort`. *)
let permute = list atom -> list atom

// high-level correctness criterion for permutations
(*| States that a permutation function `p` preserves `FStar.Tactics.CanonCommMonoidSimple.xsdenote` (up to `==`) in every commutative monoid and atom map.

    This is the correctness criterion for the reordering step of the
    canonizer; `FStar.Tactics.CanonCommMonoidSimple.permute_via_swaps_correct` establishes it. *)
let permute_correct (p:permute) =
  #a:Type -> m:cm a -> am:amap a -> xs:list atom ->
    Lemma (xsdenote m am xs == xsdenote m am (p xs))

// sufficient condition:
// permutation has to be expressible as swaps of adjacent list elements

// In the general case, an arbitrary permutation can be done via swaps.
// (see FStar.Tactics.CanonCommSwaps for a proof)


(*| Applying one adjacent swap (at an offset, as in `FStar.Tactics.CanonCommSwaps.apply_swap_aux`) gives a list of atoms with equal denotation.

    This is where commutativity and associativity of the monoid are used. *)
let rec apply_swap_aux_correct (#a:Type) (n:nat) (m:cm a) (am:amap a)
                           (xs:list atom) (s:swap (length xs + n)) :
    Lemma (requires True)
      (ensures (xsdenote m am xs == xsdenote m am (apply_swap_aux n xs s)))
      (decreases xs) =
  match xs with
  | [] | [_] -> ()
  | x1 :: x2 :: xs' ->
      if n = (s <: nat)
      then (// x1 + (x2 + xs') =a (x1 + x2) + xs'
            //                 =c (x2 + x1) + xs' = a x2 + (x1 + xs')
           let a = CM?.associativity m in
           a (select x1 am) (select x2 am) (xsdenote m am xs');
           a (select x2 am) (select x1 am) (xsdenote m am xs');
           CM?.commutativity m (select x1 am) (select x2 am))
      else apply_swap_aux_correct (n+1) m am (x2 :: xs') s

(*| Applying one adjacent swap with `FStar.Tactics.CanonCommSwaps.apply_swap` gives a list of atoms with equal denotation. *)
let apply_swap_correct (#a:Type) (m:cm a) (am:amap a)
                       (xs:list atom) (s:swap (length xs)):
    Lemma (ensures (xsdenote m am xs == xsdenote m am (apply_swap xs s)))
          (decreases xs) = apply_swap_aux_correct 0 m am xs s

(*| Applying a list of adjacent swaps with `FStar.Tactics.CanonCommSwaps.apply_swaps` gives a list of atoms with equal denotation. *)
let rec apply_swaps_correct (#a:Type) (m:cm a) (am:amap a)
                            (xs:list atom) (ss:list (swap (length xs))):
    Lemma (requires True)
      (ensures (xsdenote m am xs == xsdenote m am (apply_swaps xs ss)))
      (decreases ss) =
  match ss with
  | [] -> ()
  | s::ss' -> apply_swap_correct m am xs s;
              apply_swaps_correct m am (apply_swap xs s) ss'

(*| States that, for every list of atoms `xs`, `p xs` can be obtained from `xs` by a sequence of adjacent swaps.

    A sufficient condition for `FStar.Tactics.CanonCommMonoidSimple.permute_correct`, see
    `FStar.Tactics.CanonCommMonoidSimple.permute_via_swaps_correct`. *)
let permute_via_swaps (p:permute) =
  (#a:Type) -> (am:amap a) -> xs:list atom ->
    Lemma (exists ss. p xs == apply_swaps xs ss)

(*| A permutation that can be realized by adjacent swaps preserves the denotation of every list of atoms (up to `==`). *)
let permute_via_swaps_correct_aux (p:permute) (pvs:permute_via_swaps p)
                               (#a:Type) (m:cm a) (am:amap a) (xs:list atom) :
    Lemma (xsdenote m am xs == xsdenote m am (p xs)) =
  pvs am xs;
  assert(exists ss. p xs == apply_swaps xs ss);
  exists_elim (xsdenote m am xs == xsdenote m am (p xs))
    (() <: squash (exists ss. p xs == apply_swaps xs ss))
    (fun ss -> apply_swaps_correct m am xs ss)

(*| Every permutation that can be realized by adjacent swaps (`FStar.Tactics.CanonCommMonoidSimple.permute_via_swaps`) is correct in the sense of `FStar.Tactics.CanonCommMonoidSimple.permute_correct`. *)
let permute_via_swaps_correct
  (p:permute) (pvs:permute_via_swaps p) : permute_correct p =
     fun #a -> permute_via_swaps_correct_aux p pvs #a

(***** Sorting atoms is a correct permutation
       (since it can be done by swaps) *)

// Here we sort the variable numbers

(*| Sorts a list of atoms in increasing order of index, with `FStar.List.Tot.Base.sortWith`.

    This is the reordering used by `FStar.Tactics.CanonCommMonoidSimple.canon`. *)
let sort : permute = List.Tot.Base.sortWith #nat (compare_of_bool (<))

(*| Sorting a list of atoms can be realized by adjacent swaps.

    Proved with `FStar.Tactics.CanonCommSwaps.equal_counts_implies_swaps`, since
    `FStar.List.Tot.Base.sortWith` preserves element counts. *)
let sort_via_swaps (#a:Type) (am : amap a)  (xs:list atom)
  : Lemma (exists ss. sort xs == apply_swaps xs ss)
  =
  List.Tot.Properties.sortWith_permutation #nat (compare_of_bool (<)) xs;
  let ss = equal_counts_implies_swaps #nat xs (sort xs) in
  ()

(*| Sorting a list of atoms with `FStar.Tactics.CanonCommMonoidSimple.sort` preserves its denotation (up to `==`). *)
let sort_correct_aux (#a:Type) (m:cm a) (am:amap a) (xs:list atom) :
    Lemma (xsdenote m am xs == xsdenote m am (sort xs)) =
  permute_via_swaps_correct sort (fun #a am -> sort_via_swaps am) m am xs

(*| `FStar.Tactics.CanonCommMonoidSimple.sort` is a correct permutation in the sense of `FStar.Tactics.CanonCommMonoidSimple.permute_correct`. *)
let sort_correct : permute_correct sort = (fun #a -> sort_correct_aux #a)

(***** Canonicalization tactics *)

(* [@@plugin] *)
(*| Computes the canonical form of an expression: its atoms, units dropped, sorted by index.

    Two expressions that are equal by associativity, commutativity and the
    unit laws have the same canonical form. *)
let canon (e:exp) = sort (flatten e)

(*| An expression and its canonical form `FStar.Tactics.CanonCommMonoidSimple.canon e` have equal denotations. *)
let canon_correct (#a:Type) (m:cm a) (am:amap a) (e:exp) :
    Lemma (mdenote m am e == xsdenote m am (canon e)) =
  flatten_correct m am e; sort_correct m am (flatten e)

(*| Two expressions have equal denotations when their canonical forms do.

    The `Lemma` form of `FStar.Tactics.CanonCommMonoidSimple.monoid_reflect`. *)
let monoid_reflect_orig (#a:Type) (m:cm a) (am:amap a) (e1 e2:exp) :
  Lemma (requires (xsdenote m am (canon e1) == xsdenote m am (canon e2)))
        (ensures (mdenote m am e1 == mdenote m am e2)) =
  canon_correct m am e1; canon_correct m am e2

(*| Reduces an `==` goal between two expression denotations to the same relation between the denotations of their canonical forms.

    Stated with a `squash` argument and result so that
    `FStar.Tactics.CanonCommMonoidSimple.canon_monoid` can `apply` it to the goal. *)
let monoid_reflect (#a:Type) (m:cm a) (am:amap a) (e1 e2:exp)
    (_ : squash (xsdenote m am (canon e1) == xsdenote m am (canon e2)))
       : squash (mdenote m am e1 == mdenote m am e2) =
  canon_correct m am e1; canon_correct m am e2

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

    Defined as `FStar.Tactics.CanonCommMonoidSimple.where_aux 0`; used during reification to reuse the atom
    index of a subterm already seen. *)
let where = where_aux 0

// This expects that mult, unit, and t have already been normalized
(*| Reifies a term into an `FStar.Tactics.CanonCommMonoidSimple.exp`, extending the list of known atom terms `ts` and the atom map `am`.

    An application of an fvar that is syntactically equal to `mult` to two
    explicit arguments becomes `Mult`, and a term equal to `unit` becomes
    `Unit`. Any other term becomes an atom: a term already in `ts` reuses its
    index, a new one gets index `length ts`, is appended to `ts`, and its value
    (obtained with `unquote`) is recorded in `am`. Expects `mult`, `unit` and
    `t` to be normalized already, as done by `FStar.Tactics.CanonCommMonoidSimple.reification`. *)
let rec reification_aux (#a:Type) (ts:list term) (am:amap a)
                        (mult unit t : term) : Tac (exp & list term & amap a) =
  let hd, tl = collect_app_ref t in
  let fatom (t:term) (ts:list term) (am:amap a) : Tac (exp & list term & amap a) =
    match where t ts with
    | Some v -> (Atom v, ts, am)
    | None -> let vfresh = length ts in let z = unquote t in
              (Atom vfresh, ts @ [t], update vfresh z am)
  in
  match inspect hd, list_unref tl with
  | Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)] ->
    if term_eq (pack (Tv_FVar fv)) mult
    then (let (e1,ts,am) = reification_aux ts am mult unit t1 in
          let (e2,ts,am) = reification_aux ts am mult unit t2 in
          (Mult e1 e2, ts, am))
    else fatom t ts am
  | _, _ ->
    if term_eq t unit
    then (Unit, ts, am)
    else fatom t ts am

(*| Reifies a term into an `FStar.Tactics.CanonCommMonoidSimple.exp` for the commutative monoid `m`, returning the expression with the updated atom list and atom map.

    Normalizes `CM?.mult m`, `CM?.unit m` and the term with `delta`, `zeta`
    and `iota`, then calls `FStar.Tactics.CanonCommMonoidSimple.reification_aux`. Because of `delta`, an
    operation defined by an ordinary F\* function is unfolded and no longer
    recognized; operations such as `+` and `*` on `int` work. *)
let reification (#a:Type) (m:cm a) (ts:list term) (am:amap a) (t:term) :
    Tac (exp & list term & amap a) =
  let mult = norm_term [delta;zeta;iota] (quote (CM?.mult m)) in
  let unit = norm_term [delta;zeta;iota] (quote (CM?.unit m)) in
  let t    = norm_term [delta;zeta;iota] t in
  reification_aux ts am mult unit t

(*| Tactic that rewrites an equality goal in the commutative monoid `m` into a canonical form modulo associativity, commutativity and unit laws.

    The goal, after `norm []`, must be `t1 == t2` at a type syntactically
    equal to `a`; otherwise the tactic fails with "Goal should be an
    equality" or "Goal should be an equality at the right monoid type". Both
    sides are reified with shared atoms (see `FStar.Tactics.CanonCommMonoidSimple.reification`), the goal is
    changed to an equality of `FStar.Tactics.CanonCommMonoidSimple.mdenote` terms, `FStar.Tactics.CanonCommMonoidSimple.monoid_reflect` is
    applied, and the result is normalized. The remaining goal equates the
    right-associated products of the sorted atoms of each side, with units
    removed.

    The tactic does not close that goal: follow it with
    `FStar.Tactics.V2.Derived.trefl` when both sides
    should be identical, or leave it to SMT.

    ```fstar
    let comm_plus (a b c: int) =
      assert (a + (b + 0) + c == c + (b + a))
        by (CMS.canon_monoid FStar.Algebra.CommMonoid.int_plus_cm; trefl ())
    ```

    See `FStar.Tactics.CanonCommMonoidSimple.Equiv.canon_monoid` for monoids
    up to an equivalence relation, `FStar.Tactics.CanonCommMonoid` for a
    canonizer with more features, and `FStar.Tactics.CanonMonoid.canon_monoid`
    for monoids that are not commutative. *)
let canon_monoid (#a:Type) (m:cm a) : Tac unit =
  norm [];
  match term_as_formula (cur_goal ()) with
  | Comp (Eq (Some t)) t1 t2 ->
      // dump ("t1 =" ^ term_to_string t1 ^
      //     "; t2 =" ^ term_to_string t2);
      if term_eq t (quote a) then
        let (r1, ts, am) = reification m [] (const (CM?.unit m)) t1 in
        let (r2, _, am) = reification m ts am t2 in
         dump ("am =" ^ term_to_string (quote am));
        change_sq (quote (mdenote m am r1 == mdenote m am r2));
        // dump ("before =" ^ term_to_string (norm_term [delta;primops]
        //   (quote (mdenote m am r1 == mdenote m am r2))));
        // dump ("expected after =" ^ term_to_string (norm_term [delta;primops]
        //   (quote (xsdenote m am (canon r1) ==
        //           xsdenote m am (canon r2)))));
        apply (`monoid_reflect);
        // dump ("after apply");
        norm [delta_only [`%canon; `%xsdenote; `%flatten; `%sort;
                `%select; `%assoc; `%fst; `%Mktuple2?._1;
                `%(@); `%append; `%List.Tot.sortWith;
                `%List.Tot.partition; `%bool_of_compare; `%compare_of_bool;
           ]; primops]
        // ;dump "done"
      else fail "Goal should be an equality at the right monoid type"
  | _ -> fail "Goal should be an equality"
