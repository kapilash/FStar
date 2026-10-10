module DocsUlibCanon2

(* Examples from the documentation of FStar.Tactics.CanonMonoid,
   FStar.Tactics.CanonCommMonoidSimple, FStar.Tactics.CanonCommMonoidSimple.Equiv,
   FStar.Tactics.CanonCommSwaps and FStar.Tactics.BV *)

open FStar.List.Tot
open FStar.Tactics.V2

module CM = FStar.Tactics.CanonMonoid
module CMS = FStar.Tactics.CanonCommMonoidSimple
module CME = FStar.Tactics.CanonCommMonoidSimple.Equiv

let reassoc (a b c d: int) =
  assert (a + ((b + 0) + (c + d)) == ((a + b) + c) + d)
    by (CM.canon_monoid FStar.Algebra.Monoid.int_plus_monoid; trefl ())

let comm_plus (a b c: int) =
  assert (a + (b + 0) + c == c + (b + a))
    by (CMS.canon_monoid FStar.Algebra.CommMonoid.int_plus_cm; trefl ())

let comm_plus_equiv (a b c: int) =
  assert (a + (b + 0) + c == c + (b + a))
    by (CME.canon_monoid (`FStar.Algebra.CommMonoid.Equiv.equality_equiv int)
                         (`FStar.Algebra.CommMonoid.Equiv.int_plus_cm))

let swapped : unit =
  assert (FStar.Tactics.CanonCommSwaps.apply_swaps [1; 2; 3] [0; 1] == [2; 3; 1])

let logand_comm (x y: FStar.UInt.uint_t 64) =
  assert (FStar.UInt.logand x y == FStar.UInt.logand y x)
    by (FStar.Tactics.BV.bv_tac ())
