module FStar.Cardinality.Universes

open FStar.Functions
open FStar.Cardinality.Cantor

(*| There is no injection from a universe into a strictly smaller one.

    The larger universe is written `max (a+1) b`, which stands for an
    arbitrary universe above `a`, since sums of universe levels cannot be
    written. See `FStar.Cardinality.Universes.no_inj_universes_suc` for the
    simpler `a+1` case. *)
val no_inj_universes (f : Type u#(max (a+1) b) -> Type u#a)
  : Lemma (~(is_inj f))

(*| There is no injection from `Type u#(a+1)` into `Type u#a`.

    The special case of `FStar.Cardinality.Universes.no_inj_universes` for
    the successor universe. *)
val no_inj_universes_suc (f : Type u#(a+1) -> Type u#a)
  : Lemma (~(is_inj f))
