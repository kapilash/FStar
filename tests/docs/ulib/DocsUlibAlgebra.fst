module DocsUlibAlgebra

(* Examples from the documentation of FStar.Algebra.CommMonoid,
   FStar.Algebra.CommMonoid.Fold and FStar.BigOps *)

open FStar.Algebra.CommMonoid

let max_nat (x y: nat) : nat = if x >= y then x else y

let max_nat_cm : cm nat =
  CM #nat 0 max_nat (fun _ -> ()) (fun _ _ _ -> ()) (fun _ _ -> ())

module CE = FStar.Algebra.CommMonoid.Equiv
module CF = FStar.Algebra.CommMonoid.Fold

let id_int (i: int) : int = i

let sum_0_to_2 () : Lemma (CF.fold CE.int_plus_cm 0 2 id_int == 3) =
  CF.fold_snoc_decomposition CE.int_plus_cm 0 2 id_int;
  CF.fold_snoc_decomposition CE.int_plus_cm 0 1 id_int;
  CF.fold_singleton_lemma CE.int_plus_cm 0 id_int

let all_positive () : Lemma (FStar.BigOps.big_and (fun (x: int) -> x > 0) [1; 2; 3]) = ()

let all_positive' (l: list nat)
  : Lemma (requires FStar.BigOps.big_and' (fun (x: nat) -> x > 0) l)
          (ensures forall x. FStar.List.Tot.memP x l ==> x > 0)
  = FStar.BigOps.big_and'_forall (fun (x: nat) -> x > 0) l
