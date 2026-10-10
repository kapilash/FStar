(*
   Copyright 2015 Chantal Keller and Catalin Hritcu, Microsoft Research and Inria

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Chantal Keller, Catalin Hritcu, Aseem Rastogi, Nikhil Swamy
*)

(* Defining accessibility predicates and well-founded recursion like in Coq
   https://coq.inria.fr/library/Coq.Init.Wf.html
*)

module FStar.WellFounded

#set-options "--warn_error -242" //inner let recs not encoded to SMT; ok

(*| A binary relation on `a`, as a `prop`-valued function. *)
let binrel (a:Type) = a -> a -> prop

(*
 * The accessibility relation
 * -- Marked erasable, since this is a singleton type anyway
 * -- Erasability also simplifies proofs that use accessibility in
 *    with axioms like indefinitedescription
 *)
(*| The accessibility predicate of a relation `r`: `acc r x` holds when every
    descending `r`-chain starting from `x` is finite.

    Its single constructor `AccIntro` takes a field `access_smaller` that,
    for every `y` with `r y x`, gives a proof of `acc r y`. Because `acc` is
    inductive, a proof of `acc r x` can be used as a decreasing measure, which
    is how `FStar.WellFounded.fix_F` is defined. The type is `erasable`: it
    has no computational content. *)
[@@ erasable]
noeq
type acc (#a:Type u#a) (r:binrel u#a a) (x:a) : Type u#a =
  | AccIntro : access_smaller:(y:a -> squash (r y x) -> acc r y) -> acc r x

(*| A relation `r` is well-founded when every element is accessible, as
    witnessed by a function returning `acc r x` for each `x`.

    This is the constructive form; `FStar.WellFounded.is_well_founded` is the
    propositional one. Building blocks to obtain one include
    `FStar.WellFounded.subrelation_wf`, `FStar.WellFounded.inverse_image_wf`
    and `FStar.LexicographicOrdering.lex_t_wf`. *)
[@@ erasable]
let well_founded (#a:Type u#a) (r:binrel u#a a) = x:a -> acc r x

(*| Well-founded recursion on an accessibility proof: computes `p x` from a
    step function `f` that may call itself on any `y` with `r y x`.

    The recursion decreases on the proof `a : acc r x`. Usually
    `FStar.WellFounded.fix` is more convenient. *)
let rec fix_F (#aa:Type) (#r:binrel aa) (#p:(aa -> Type))
              (f: (x:aa -> (y:aa -> r y x -> p y) -> p x))
              (x:aa) (a:acc r x)
  : Tot (p x) (decreases a)
  = f x (fun y h -> fix_F f y (a.access_smaller y h))

(*| The well-founded fixpoint combinator: given a proof that `r` is
    well-founded, defines a dependent function `x:aa -> p x` by a step
    function that may recursively call itself on any `y` with `r y x`.

    ```fstar
    let lt_nat : FStar.WellFounded.binrel nat = fun x y -> x < y

    let rec lt_nat_acc (n:nat) : Tot (FStar.WellFounded.acc lt_nat n) (decreases n) =
      FStar.WellFounded.AccIntro (fun m _ -> lt_nat_acc m)

    let sum_to (n:nat) : nat =
      FStar.WellFounded.fix lt_nat_acc (fun _ -> nat)
        (fun n rec_call -> if n = 0 then 0 else n + rec_call (n - 1) ())
        n
    ```

    Alternatively, an `acc` proof or `FStar.WellFoundedRelation.wfr_t` can
    be used directly in a `decreases` clause. *)
let fix (#aa:Type) (#r:binrel aa) (rwf:well_founded r)
        (p:aa -> Type) (f:(x:aa -> (y:aa -> r y x -> p y) -> p x))
        (x:aa)
  : p x
  = fix_F f x (rwf x)


(*| The propositional form of well-foundedness: every element of `a` is
    accessible (`acc rel x` is nonempty).

    Obtained from a constructive proof by
    `FStar.WellFounded.is_well_founded_of_well_founded`. *)
let is_well_founded (#a:Type) (rel:binrel a) =
  forall (x:a). nonempty (acc rel x)

(*| A relation on `a` together with a (propositional) proof that it is
    well-founded.

    Built with `FStar.WellFounded.as_well_founded` or
    `FStar.WellFounded.subrelation_as_wf`. *)
let well_founded_relation (a:Type) = rel:binrel a{is_well_founded rel}

(*| Packages a constructive well-foundedness proof as a
    `FStar.WellFounded.well_founded_relation`; the result is the relation
    `rel` itself. *)
unfold
let as_well_founded (#a:Type u#a)
                    (#rel:binrel u#a a)
                    (f:well_founded rel)
  : well_founded_relation a
  = introduce forall (x:a). nonempty (acc rel x)
    with nonempty_intro (f x);
    rel

(*
 * Proofs that subrelation and inverse image commute with well-foundedness
 *
 * Reference: Constructing Recursion Operators in Type Theory, L. Paulson  JSC (1986) 2, 325-355
 *)
(*| A subrelation of a well-founded relation is well-founded: if every pair
    related by `sub_r` is related by `r`, and `r` is well-founded, so is
    `sub_r`.

    See `FStar.WellFounded.subrelation_squash_wf` for the propositional form. *)
let subrelation_wf (#a:Type) (#r #sub_r:binrel a)
  (sub_w:(x:a -> y:a -> sub_r x y -> r x y))
  (r_wf:well_founded r)
  : well_founded sub_r
  = let rec aux (x:a) (acc_r:acc r x) : Tot (acc sub_r x) (decreases acc_r) =
      AccIntro (fun y sub_r_y_x ->
        aux y
          (match acc_r with
           | AccIntro f -> f y (sub_w y x sub_r_y_x))) in
    fun x -> aux x (r_wf x)

(*| A subrelation of a well-founded relation is well-founded, stated as the
    proposition `FStar.WellFounded.is_well_founded sub_r`.

    The constructive form is `FStar.WellFounded.subrelation_wf`. *)
let subrelation_squash_wf (#a:Type u#a)
                          (#r:binrel u#a a)
                          (#sub_r:binrel u#a a)
                          (sub_w:(x:a -> y:a -> sub_r x y -> r x y))
                          (r_wf:well_founded r)
  : Lemma (is_well_founded sub_r)
  = introduce forall (x:a). nonempty (acc sub_r x)
    with (
      let rec acc_y (x:a) (acc_r:acc r x) (y:a) (p:sub_r y x)
        : Tot (acc sub_r y)
              (decreases acc_r)
        = AccIntro (acc_y y (acc_r.access_smaller
                                   y
                                   (sub_w y x p)))
      in
      nonempty_intro (AccIntro (acc_y x (r_wf x)))
    )

(*| A constructive well-foundedness proof implies the propositional one,
    `FStar.WellFounded.is_well_founded r`. *)
let is_well_founded_of_well_founded #a (#r: binrel u#a a) (r_wf: well_founded r) :
    Lemma (is_well_founded r) =
  subrelation_squash_wf #a #r #r (fun _ _ _ -> ()) r_wf

(*| Returns `sub_r` as a `FStar.WellFounded.well_founded_relation`, given that
    it is included in the well-founded relation `r`.

    Unlike `FStar.WellFounded.subrelation_wf`, the inclusion proof only needs
    to give a squashed `r x y`. *)
unfold
let subrelation_as_wf (#a:Type u#a) (#r #sub_r:binrel u#a a)
  (sub_w:(x:a -> y:a -> sub_r x y -> squash (r x y)))
  (r_wf:well_founded r)
  : well_founded_relation a
  = subrelation_squash_wf sub_w r_wf;
    sub_r

(*| The inverse image of a relation `r_b` on `b` under `f : a -> b`: `x` is
    related to `y` when `r_b (f x) (f y)`.

    This is how a measure function turns into a relation; see
    `FStar.WellFounded.inverse_image_wf`. *)
let inverse_image (#a:Type u#a) (#b:Type u#b) (r_b:binrel u#b b) (f:a -> b) : binrel u#a a =
  fun x y -> r_b (f x) (f y)

(*| The inverse image of a well-founded relation under any function is
    well-founded.

    For example, ordering values by a `nat`-valued measure is well-founded. *)
let inverse_image_wf (#a:Type u#a) (#b:Type u#b) (#r_b:binrel u#b b)
  (f:a -> b)
  (r_b_wf:well_founded r_b)
  : well_founded (inverse_image r_b f)
  = let rec aux (x:a) (acc_r_b:acc r_b (f x))
      : Tot (acc (inverse_image r_b f) x)
            (decreases acc_r_b) =
      AccIntro #_ #(inverse_image r_b f) fun y p ->
        aux y (acc_r_b.access_smaller (f y) p)
    in
    fun x -> aux x (r_b_wf (f x))
