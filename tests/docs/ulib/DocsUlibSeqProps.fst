module DocsUlibSeqProps

(* Examples from the documentation of FStar.Seq.Properties, FStar.Seq.Sorted
   and FStar.Seq.Permutation *)

let abc : FStar.Seq.Base.seq int = FStar.Seq.Properties.createL [1; 2; 3]

let _ = assert (FStar.Seq.Base.length abc == 3)

let swap_ends (s: FStar.Seq.Base.seq int{FStar.Seq.Base.length s > 0})
  : Lemma (FStar.Seq.Properties.permutation int s
             (FStar.Seq.Properties.swap s 0 (FStar.Seq.Base.length s - 1)))
  = FStar.Seq.Properties.lemma_swap_permutes s 0 (FStar.Seq.Base.length s - 1)

let sort_ints (#n: nat) (s: FStar.Seq.Properties.lseq int n)
  : FStar.Seq.Properties.lseq int n
  = FStar.Seq.Properties.sort_lseq (fun x y -> x <= y) s

let int_le (x y: int) : bool = x <= y

let sorted_first_le_last (s: FStar.Seq.Base.seq int{FStar.Seq.Base.length s > 0})
  : Lemma (requires FStar.Seq.Properties.sorted int_le s)
          (ensures int_le (FStar.Seq.Base.index s 0) (FStar.Seq.Properties.last s))
  = FStar.Seq.Sorted.sorted_sorted_pred_lemma int_le s
