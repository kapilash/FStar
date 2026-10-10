module DocsUlibRational

(* Examples from the documentation of FStar.Rational, FStar.Real and
   FStar.Real.Dedekind *)

module Q = FStar.Rational

let half_plus_half () : Lemma (Q.add (Q.mk 1 2) (Q.mk 1 2) == Q.one) =
  Q.mk_add 1 2 1 2;
  Q.of_int_mk 1;
  Q.mk_eq 4 4 1 1

let two_is_one_plus_one () : Lemma (Q.two == Q.add Q.one Q.one) =
  Q.of_int_add 1 1

open FStar.Real

let _ = assert (1.0R +. 1.0R == 2.0R)
let _ = assert (forall (x:real). x >. 0.0R ==> x /. 2.0R <. x)

module D = FStar.Real.Dedekind

let sum_comm4 (a b c d:D.real)
  : Lemma (D.add (D.add a b) (D.add c d) == D.add (D.add c d) (D.add a b)) =
  D.add_comm (D.add a b) (D.add c d)
