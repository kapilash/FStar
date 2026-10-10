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
module FStar.Tactics.Logic.Lemmas

(*| Proves `forall (x:a). p x` from a function giving a proof of `p x` for
    every `x`; the lemma behind `FStar.Tactics.V2.Logic.forall_intro`. *)
val fa_intro_lem (#a:Type) (#p:a -> prop) (f:(x:a -> squash (p x))) : Lemma (forall (x:a). p x)

(*| Proves `a /\ b` from proofs of `a` and of `b`; the lemma behind
    `FStar.Tactics.V2.Logic.split`. *)
val split_lem : (#a:prop) -> (#b:prop) ->
                        squash a -> squash b -> Lemma (a /\ b)
(*| Proves `a ==> b` from a function turning a proof of `a` into a proof of
    `b`; the lemma behind `FStar.Tactics.V2.Logic.implies_intro`. *)
val imp_intro_lem : (#a:prop) -> (#b : prop) ->
                            (squash a -> squash b) ->
                            Lemma (a ==> b)
(*| Turns a lemma `unit -> Lemma (requires req) (ensures ens)` and a proof
    of `req` into a proof of `squash ens`. *)
val __lemma_to_squash (#req #ens : prop) (_ : squash req) (h : (unit -> Lemma (requires req) (ensures ens))) : squash ens

(*| Modus ponens on squashed propositions: from a proof of `p` and a
    function from proofs of `p` to proofs of `q`, proves `q`. *)
val vbind : (#p:prop) -> (#q:prop) -> squash p -> (squash p -> squash q) -> Lemma q

(*| Case analysis on a disjunction: from `p \/ q`, `p ==> phi` and
    `q ==> phi`, proves `phi`; the lemma behind
    `FStar.Tactics.V2.Logic.cases_or`. *)
val or_ind : (#p:prop) -> (#q:prop) -> (#phi:prop) ->
                     squash (p \/ q) ->
                     (squash (p ==> phi)) ->
                     (squash (q ==> phi)) ->
                     Lemma phi

(*| Case analysis on a boolean `b`: from `b == true ==> phi` and
    `b == false ==> phi`, proves `phi`; the lemma behind
    `FStar.Tactics.V2.Logic.cases_bool`. *)
val bool_ind : (b:bool) -> (phi:prop) -> (squash (b == true  ==> phi)) ->
                                                 (squash (b == false ==> phi)) ->
                                                 Lemma phi

(*| Proves `p \/ q` from a proof of `p`; the lemma behind
    `FStar.Tactics.V2.Logic.left`. *)
val or_intro_1 : (#p:prop) -> (#q:prop) -> squash p -> Lemma (p \/ q)

(*| Proves `p \/ q` from a proof of `q`; the lemma behind
    `FStar.Tactics.V2.Logic.right`. *)
val or_intro_2 : (#p:prop) -> (#q:prop) -> squash q -> Lemma (p \/ q)

(*| Conjunction elimination: from `p /\ q` and `p ==> q ==> phi`, proves
    `phi`; the lemma behind `FStar.Tactics.V2.Logic.and_elim`.

    `FStar.Tactics.Logic.Lemmas.__and_elim'` has the same statement and is
    tried by `and_elim` when this one fails to apply. *)
val __and_elim : (#p:prop) -> (#q:prop) -> (#phi:prop) ->
                              squash (p /\ q) ->
                              squash (p ==> q ==> phi) ->
                              Lemma phi

(*| Conjunction elimination, with the same statement as
    `FStar.Tactics.Logic.Lemmas.__and_elim`; used as a fallback by
    `FStar.Tactics.V2.Logic.and_elim`. *)
val __and_elim' : (#p:prop) -> (#q:prop) -> (#phi:prop) ->
                              squash (p /\ q) ->
                              squash (p ==> q ==> phi) ->
                              Lemma phi

(*| Proves `exists (x:a). p x` from a witness `x` and a proof of `p x`; the
    lemma behind `FStar.Tactics.V2.Logic.witness`. *)
val __witness : (#a:Type) -> (x:a) -> (#p:(a -> prop)) -> squash (p x) -> squash (exists (x:a). p x)

(*| Existential elimination: from `exists x. pred x` and a proof of `goal`
    for any `x` satisfying `pred x`, proves `goal`; the lemma behind
    `FStar.Tactics.V2.Logic.elim_exists`. *)
val __elim_exists' #t (#pred : t -> prop) #goal (h : squash (exists x. pred x))
                          (k : (x:t -> squash (pred x) -> squash goal)) : squash goal

(*| Instantiates a proof of `forall x. pred x` at a given `x`, giving
    `pred x`; used by `FStar.Tactics.V2.Logic.instantiate`.

    `FStar.Tactics.Logic.Lemmas.__forall_inst_sq` has the same statement. *)
val __forall_inst #t (#pred : t -> prop) (h : squash (forall x. pred x)) (x : t) : squash (pred x)

(*| Instantiates a proof of `forall x. pred x` at a given `x`, giving
    `pred x`; the same statement as
    `FStar.Tactics.Logic.Lemmas.__forall_inst`, tried first by
    `FStar.Tactics.V2.Logic.instantiate`. *)
val __forall_inst_sq #t (#pred : t -> prop) (h : squash (forall x. pred x)) (x : t) : squash (pred x)

(*| Existential elimination into a proposition: given a proof of
    `exists x. p x` and `forall x. p x ==> phi`, proves `phi`; used by
    `FStar.Tactics.V2.Logic.skolem`. *)
val sklem0 (#a:Type) (#p : a -> prop) ($v : squash (exists (x:a). p x)) (phi:prop) :
  Lemma (requires (forall x. p x ==> phi))
        (ensures phi)

(*| Turns a function proving `squash (post x)` for every `x` satisfying
    `pre x` into a lemma with precondition `pre x` and postcondition
    `post x`. *)
val lemma_from_squash (#a:Type) (#pre #post : a -> prop) :
  (x:a{pre x} -> squash (post x)) -> x:a -> Lemma (requires pre x) (ensures post x)

(*| Turns a one-argument lemma with precondition `pre x` and postcondition
    `post x` into `forall x. pre x ==> post x`; used by
    `FStar.Tactics.V2.Logic.using_lemma`. *)
val lem1_fa #a #pre #post
  ($lem : (x:a -> Lemma (requires pre x) (ensures post x))) :
  Lemma (forall (x:a). pre x ==> post x)

(*| Turns a two-argument lemma into the statement
    `forall x y. pre x y ==> post x y`; used by
    `FStar.Tactics.V2.Logic.using_lemma`. *)
val lem2_fa #a #b #pre #post
  ($lem : (x:a -> y:b -> Lemma (requires pre x y) (ensures post x y))) :
  Lemma (forall (x:a) (y:b). pre x y ==> post x y)

(*| Turns a three-argument lemma into the statement
    `forall x y z. pre x y z ==> post x y z`; used by
    `FStar.Tactics.V2.Logic.using_lemma`. *)
val lem3_fa #a #b #c #pre #post
  ($lem : (x:a -> y:b -> z:c -> Lemma (requires pre x y z) (ensures post x y z))) :
  Lemma (forall (x:a) (y:b) (z:c). pre x y z ==> post x y z)

(*| Instantiates a proof of `forall (x:a). b x` at every `x`, giving a
    function from `x` to proofs of `b x`; used by
    `FStar.Tactics.V2.Logic.l_revert` to turn a reverted binder back into a
    universal quantifier. *)
val revert_squash : (#a:Type) -> (#b : (a -> prop)) ->
                            (squash (forall (x:a). b x)) ->
                            x:a -> squash (b x)
