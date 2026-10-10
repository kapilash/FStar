module DocsUlibListProps

open FStar.All
open FStar.List.Tot

(* Examples from the documentation of FStar.List *)

let sum_of_heads (l1 l2: list int) : ML int =
  FStar.List.hd l1 + FStar.List.hd l2

(* Examples from the documentation of FStar.List.Pure.Base *)

let pairs : list (int & bool) = FStar.List.Pure.Base.zip [1; 2] [true; false]

(* Examples from the documentation of FStar.List.Pure.Properties *)

let split_then_join (l: list int) (n: nat{n <= length l})
  : Lemma (let l1, l2 = splitAt n l in l1 @ l2 == l)
  = FStar.List.Pure.Properties.lemma_splitAt_append n l

(* Examples from the documentation of FStar.List.Tot.Properties *)

let rev_rev_example (l: list int) : Lemma (rev (rev l) == l) =
  FStar.List.Tot.Properties.rev_involutive l

let length_of_append (l1 l2: list nat)
  : Lemma (length (l1 @ l2) == length l1 + length l2)
  = ()

let reassociate (l1 l2 l3: list int) : Lemma (l1 @ (l2 @ l3) == (l1 @ l2) @ l3) =
  FStar.List.Tot.Properties.append_assoc l1 l2 l3
