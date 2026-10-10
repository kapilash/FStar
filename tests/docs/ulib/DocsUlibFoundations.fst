module DocsUlibFoundations

(* Examples from the documentation of FStar.Ghost and FStar.Calc *)

let sum (x y: FStar.Ghost.erased int) : FStar.Ghost.erased int =
  let open FStar.Ghost in
  let@ a = x in
  let@ b = y in
  return (a + b)

let calc_example (a b: int) (h: squash (a == b)) : Lemma (a + 1 == b + 1) =
  calc (==) {
    a + 1;
    == { }
    b + 1;
  }
