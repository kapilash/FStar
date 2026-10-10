module DocsUlibFinite

(* Examples from the documentation of FStar.FiniteSet.Base,
   FStar.FiniteMap.Base, FStar.Sequence.Base and FStar.Sequence.Ambient *)

let two_elements ()
  : Lemma (FStar.FiniteSet.Base.cardinality
             (FStar.FiniteSet.Base.insert 1 (FStar.FiniteSet.Base.singleton 2)) = 2)
  = FStar.FiniteSet.Base.all_finite_set_facts_lemma ()

let insert_then_read (m: FStar.FiniteMap.Base.map int string)
  : Lemma (FStar.FiniteMap.Base.elements (FStar.FiniteMap.Base.insert 1 "one" m) 1 == Some "one")
  = FStar.FiniteMap.Base.all_finite_map_facts_lemma ()

let append_length (s t: FStar.Sequence.Base.seq int)
  : Lemma (FStar.Sequence.Base.length (FStar.Sequence.Base.append s t) =
           FStar.Sequence.Base.length s + FStar.Sequence.Base.length t)
  = FStar.Sequence.Base.all_seq_facts_lemma ()

open FStar.FiniteSet.Ambient
let singleton_has_its_element (x: int)
  : Lemma (FStar.FiniteSet.Base.mem x (FStar.FiniteSet.Base.singleton x))
  = ()

open FStar.FiniteMap.Ambient
let insert_grows_domain (m: FStar.FiniteMap.Base.map int string)
  : Lemma (FStar.FiniteMap.Base.mem 1 (FStar.FiniteMap.Base.insert 1 "one" m))
  = ()

open FStar.Sequence
let build_then_index (s: seq int)
  : Lemma ((s $:: 0) $@ length s == 0)
  = ()

let take_of_append (s t: seq int)
  : Lemma (take (s $+ t) (length s) == s)
  = ()
