module DocsUlibSeq

(* Examples from the documentation of FStar.Seq.Base *)

let middle (s: FStar.Seq.Base.seq int{FStar.Seq.Base.length s = 4})
  : int
  = FStar.Seq.Base.index (FStar.Seq.Base.slice s 1 3) 0

let _ = assert (forall (s: FStar.Seq.Base.seq int{FStar.Seq.Base.length s = 4}).
                  middle s == FStar.Seq.Base.index s 1)
