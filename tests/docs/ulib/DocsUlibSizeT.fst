module DocsUlibSizeT

(* Examples from the documentation of FStar.SizeT, FStar.PtrdiffT,
   FStar.UInt128 and FStar.Integers *)

let small_size : FStar.SizeT.t = FStar.SizeT.uint_to_t 1000

let sum_sizes (x y: FStar.SizeT.t)
  : Pure FStar.SizeT.t
    (requires FStar.SizeT.fits (FStar.SizeT.v x + FStar.SizeT.v y))
    (ensures fun z -> FStar.SizeT.v z == FStar.SizeT.v x + FStar.SizeT.v y)
  = FStar.SizeT.add x y

let pred_size (x: FStar.SizeT.t{FStar.SizeT.v x > 0}) : FStar.SizeT.t =
  FStar.SizeT.(x - 1sz)

let widen_u32 (x: FStar.UInt32.t)
  : Pure FStar.SizeT.t
    (requires FStar.SizeT.fits_u32)
    (ensures fun y -> FStar.SizeT.v y == FStar.UInt32.v x)
  = FStar.SizeT.uint32_to_sizet x

let hundred : FStar.PtrdiffT.t = FStar.PtrdiffT.mk 100s

let to_size (x: FStar.PtrdiffT.t{FStar.PtrdiffT.v x >= 0}) : FStar.SizeT.t =
  FStar.PtrdiffT.ptrdifft_to_sizet x

let wide_product (x y: FStar.UInt64.t)
  : r:FStar.UInt128.t{FStar.UInt128.v r == FStar.UInt64.v x * FStar.UInt64.v y}
  = FStar.UInt128.mul_wide x y

let incr_wraps (x: FStar.UInt128.t)
  : Lemma (FStar.UInt128.v (FStar.UInt128.add_mod x (FStar.UInt128.uint_to_t 1))
           == (FStar.UInt128.v x + 1) % pow2 128)
  = ()

let low_half (x: FStar.UInt128.t)
  : r:FStar.UInt64.t{FStar.UInt64.v r == FStar.UInt128.v x % pow2 64}
  = FStar.UInt128.uint128_to_uint64 x

open FStar.Integers

let add_u32 (x: uint_32) (y: uint_32{ok (+) x y}) : uint_32 = x + y

let wrap_u8 (x y: uint_8) : uint_8 = x +% y

let widen_u8 (x: uint_8) : uint_32 = cast x
