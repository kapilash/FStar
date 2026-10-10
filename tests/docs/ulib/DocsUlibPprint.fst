module DocsUlibPprint

(* Examples from the documentation of FStar.Pprint, FStar.RBSet, FStar.RBMap,
   FStar.FunctionalQueue, FStar.PartialMap and FStar.DependentMap *)

open FStar.Class.Ord.Raw

let call_doc (f: string) (args: list string) : FStar.Pprint.document =
  let open FStar.Pprint in
  group (doc_of_string f ^^ parens (separate_map (comma ^^ break_ 1) doc_of_string args))

let block_doc (body: list FStar.Pprint.document) : FStar.Pprint.document =
  let open FStar.Pprint in
  surround_separate 2 1 (lbrace ^^ rbrace) lbrace (semi ^^ break_ 1) rbrace body

let small_set : FStar.RBSet.t int = FStar.RBSet.from_list [3; 1; 2]
let has_two : bool = FStar.RBSet.mem 2 small_set

let ages : FStar.RBMap.t string int = FStar.RBMap.from_list [("alice", 30); ("bob", 25)]
let bob_age : option int = FStar.RBMap.lookup "bob" ages

let peek_after_enqueue (x: int)
  : Lemma (FStar.FunctionalQueue.peek (FStar.FunctionalQueue.enqueue x FStar.FunctionalQueue.empty) == x)
  = ()

let pm : FStar.PartialMap.t int string = FStar.PartialMap.upd (FStar.PartialMap.empty int string) 1 "one"
let _ = assert (FStar.PartialMap.sel pm 1 == Some "one" /\ FStar.PartialMap.sel pm 2 == None)

let dv (b: bool) : Type0 = if b then int else string
let dm_init (b: bool) : dv b = if b then 0 else "zero"
let dm : FStar.DependentMap.t bool dv = FStar.DependentMap.create dm_init
let _ = assert (FStar.DependentMap.sel (FStar.DependentMap.upd dm true 1) true == 1)
