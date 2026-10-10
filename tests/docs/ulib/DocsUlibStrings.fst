module DocsUlibStrings

(* Examples from the documentation of FStar.String, FStar.Vector.Base and FStar.Fin *)

let _ = assert_norm (FStar.String.strlen "hello" == 5)

let _ = assert_norm (FStar.String.list_of_string "ab" == ['a'; 'b'])

let concat_len (s1 s2: string)
  : Lemma (FStar.String.strlen (s1 ^ s2) = FStar.String.strlen s1 + FStar.String.strlen s2)
  = FStar.String.concat_length s1 s2

let squares : FStar.Vector.Base.raw int 4ul =
  FStar.Vector.Base.init 4ul (fun i -> i * i)

let _ = assert (FStar.Vector.Base.index squares 3ul == 9)

let collision (s: FStar.Seq.seq (FStar.Fin.under 3){FStar.Seq.length s = 4})
  : GTot (i: nat & j: nat{i < j /\ j < 4})
  = let (i, j) = FStar.Fin.pigeonhole s in
    (| i, j |)

let _ = FStar.Fin.is_reflexive_intro #int (fun x y -> x = y)
