module DocsUlibBytes

(* Examples from the documentation of FStar.Bytes, FStar.Endianness,
   FStar.RealLiteral, FStar.RealLiteral.Parse and FStar.ImmutableArray *)

let zeros : FStar.Bytes.lbytes 3 = FStar.Bytes.create 3ul 0uy

let _ = assert (FStar.Bytes.get zeros 1ul == 0uy)

let _ = assert (FStar.Endianness.le_to_n (FStar.Endianness.n_to_le 2 258) == 258)

let _ = assert_norm (FStar.RealLiteral.mk 150 (-2) == FStar.RealLiteral.mk 15 (-1))

let _ = assert_norm (FStar.RealLiteral.to_string (FStar.RealLiteral.mk 15 (-1)) == "1.5")

let _ = assert_norm (FStar.RealLiteral.Parse.of_string "1.50" == Some (FStar.RealLiteral.mk 15 (-1)))

let _ = assert_norm (FStar.ImmutableArray.length (FStar.ImmutableArray.of_list [10; 20; 30]) == 3)

let _ = assert_norm (FStar.ImmutableArray.index (FStar.ImmutableArray.of_list [10; 20; 30]) 1 == 20)
