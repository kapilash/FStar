module DocsUlibList

(* Examples from the documentation of FStar.List.Tot.Base *)

let third : int = FStar.List.Tot.Base.index [10; 20; 30] 2

let _ = assert_norm (third == 30)
