module DocsUlibNorm

(* Examples from the documentation of FStar.NormSteps *)

let f0 = 0
let f1 = f0 + 1

let _ = assert (norm [delta_only [`%f1]] f1 == f0 + 1)
let _ = assert (norm [delta_fully [`%f1]] f1 == 0 + 1)

irreducible let my_attr = ()

[@@my_attr]
let g0 = 0
[@@my_attr]
let g1 = g0 + 1

let _ = assert (norm [delta_attr [`%my_attr]] g1 == 0 + 1)
