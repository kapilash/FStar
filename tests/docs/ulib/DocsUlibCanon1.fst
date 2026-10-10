module DocsUlibCanon1

(* Examples from the documentation of FStar.Tactics.CanonCommSemiring,
   FStar.Tactics.CanonCommMonoid and FStar.Tactics.Canon *)

let ring_example (a b : int) =
  assert ((a + b) * (a + b) == a * a + 2 * a * b + b * b)
    by (FStar.Tactics.CanonCommSemiring.int_semiring ())

let ring_opp_example (x y : int) =
  assert ((x + - y) * (x + y) == x * x + - (y * y))
    by (FStar.Tactics.CanonCommSemiring.canon_semiring FStar.Tactics.CanonCommSemiring.int_cr)

let monoid_example (a b c : int) =
  assert (a + (b + c) == c + (b + a))
    by (FStar.Tactics.CanonCommMonoid.canon_monoid FStar.Algebra.CommMonoid.int_plus_cm;
        FStar.Tactics.V2.Derived.trefl ())

let monoid_const_example (a b : int) =
  assert (a + 2 + b == b + (1 + a) + 1)
    by (FStar.Tactics.CanonCommMonoid.canon_monoid_const FStar.Algebra.CommMonoid.int_plus_cm)

let canon_example (x y z : int) =
  assert (x * (y + z) == z * x + y * x)
    by (FStar.Tactics.Canon.canon ())
