module DocsUlibSets

(* Examples from the documentation of FStar.Set, FStar.Map, FStar.OrdSet
   and FStar.OrdMap *)

let union_comm (s1 s2: FStar.Set.set int)
  : Lemma (FStar.Set.union s1 s2 == FStar.Set.union s2 s1)
  = assert (FStar.Set.equal (FStar.Set.union s1 s2) (FStar.Set.union s2 s1))

let _ = assert (FStar.Set.mem 2 (FStar.Set.as_set [1; 2; 3]))

let m : FStar.Map.t int string = FStar.Map.upd (FStar.Map.const "") 1 "one"
let _ = assert (FStar.Map.sel m 1 == "one" /\ FStar.Map.sel m 2 == "")

let int_le : FStar.OrdSet.cmp int = fun x y -> x <= y
let s12 : FStar.OrdSet.ordset int int_le =
  FStar.OrdSet.union (FStar.OrdSet.singleton 1) (FStar.OrdSet.singleton 2)
let _ = assert (FStar.OrdSet.mem 2 s12 /\ not (FStar.OrdSet.mem 3 s12))

let om : FStar.OrdMap.ordmap int string int_le =
  FStar.OrdMap.update 1 "one" FStar.OrdMap.empty
let _ = assert (FStar.OrdMap.select 1 om == Some "one" /\ FStar.OrdMap.select 2 om == None)
