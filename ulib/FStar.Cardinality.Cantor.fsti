module FStar.Cardinality.Cantor

(* Cantor's theorem: there is no surjection from a set to its
powerset, and therefore also no injection from the powerset to the
set. *)

open FStar.Functions

(*| Cantor's theorem: no function from `a` to its powerset
    `FStar.Functions.powerset a` is surjective. *)
val no_surj_powerset (a : Type) (f : a -> powerset a)
  : Lemma (~(is_surj f))

(*| There is no injection from the powerset `FStar.Functions.powerset a` into
    `a`; a consequence of `FStar.Cardinality.Cantor.no_surj_powerset`. *)
val no_inj_powerset (a : Type) (f : powerset a -> a)
  : Lemma (~(is_inj f))
