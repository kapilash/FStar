module DocsUlibInt

(* Examples from the documentation of FStar.Int, FStar.Int.Cast and
   FStar.Int.Cast.Full *)

open FStar.Int

let wrap_example () : Lemma (add_mod #8 127 1 == -128 /\ 200 @% 256 == -56) =
  assert_norm (add_mod #8 127 1 == -128 /\ 200 @% 256 == -56)

let truncating_division () : Lemma ((-7) /- 2 == -3 /\ mod #8 (-7) 2 == -1) =
  assert_norm ((-7) /- 2 == -3 /\ mod #8 (-7) 2 == -1)

let sign_extend (x:FStar.Int8.t)
  : Lemma (FStar.Int32.v (FStar.Int.Cast.int8_to_int32 x) == FStar.Int8.v x)
  = ()

let minus_one_as_byte (x:FStar.Int32.t{FStar.Int32.v x == -1})
  : Lemma (FStar.UInt8.v (FStar.Int.Cast.int32_to_uint8 x) == 255)
  = ()

let truncate_to_byte (x:FStar.UInt32.t{FStar.UInt32.v x == 0x1234})
  : Lemma (FStar.UInt8.v (FStar.Int.Cast.uint32_to_uint8 x) == 0x34)
  = ()

let widen_then_narrow (x:FStar.UInt64.t)
  : Lemma (FStar.Int.Cast.Full.uint128_to_uint64
             (FStar.Int.Cast.Full.uint64_to_uint128 x) == x)
  = FStar.Math.Lemmas.small_mod (FStar.UInt64.v x) (pow2 64);
    FStar.UInt64.v_inj (FStar.Int.Cast.Full.uint128_to_uint64
                          (FStar.Int.Cast.Full.uint64_to_uint128 x)) x
