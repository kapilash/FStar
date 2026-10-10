module DocsUlibBVClass

(* Examples from the documentation of FStar.BitVector, FStar.BV and the
   FStar.Class.* typeclass modules *)

let logand_vec_self (#n: pos) (a: FStar.BitVector.bv_t n)
  : Lemma (FStar.BitVector.logand_vec a a == a)
  = FStar.Seq.Base.lemma_eq_intro (FStar.BitVector.logand_vec a a) a

let bvand_comm_32 (x y: FStar.BV.bv_t 32)
  : Lemma (FStar.BV.bvand x y == FStar.BV.bvand y x)
  = ()

let int2bv_roundtrip (x: FStar.UInt.uint_t 16)
  : Lemma (FStar.BV.bv2int #16 (FStar.BV.int2bv #16 x) == x)
  = FStar.BV.inverse_num_lemma #16 x

open FStar.Class.Add

let sum (#a: Type) {| additive a |} (xs: list a) : a =
  FStar.List.Tot.Base.fold_right (++) xs zero

let _ = assert_norm (sum [1; 2; 3] == 6)

let _ = assert_norm (sum [[1]; [2; 3]] == [1; 2; 3])

open FStar.Class.TotalOrder.Raw

let _ = assert_norm (compare [1; 2] [1; 3] == FStar.Order.Lt)

let _ = assert_norm (Some 1 < Some 2)

let _ = assert_norm (FStar.Class.Printable.to_string #(option int & bool) (Some 1, true) == "((Some 1), true)")

let eq_lists () : Lemma (FStar.Class.Eq.eq [1; 2] [1; 2] == true) =
  assert_norm (FStar.Class.Eq.eq [1; 2] [1; 2] == true)
