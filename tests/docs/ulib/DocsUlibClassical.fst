module DocsUlibClassical

(* Examples from the documentation of FStar.Classical *)

let pos_square (x: int)
  : Lemma (requires x > 0) (ensures x * x > 0)
  = ()

let square_if_pos (x: int) : Lemma (x > 0 ==> x * x > 0) =
  FStar.Classical.move_requires pos_square x

let double_nonneg (x: nat) : Lemma (x + x >= 0) = ()

let all_doubles_nonneg () : Lemma (forall (x: nat). x + x >= 0) =
  FStar.Classical.forall_intro double_nonneg
