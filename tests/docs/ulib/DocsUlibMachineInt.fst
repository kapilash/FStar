module DocsUlibMachineInt

(* Checked examples for the generated fixed-width integer modules
   (FStar.UInt8/16/32/64 and FStar.Int8/16/32/64/128). *)

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module I8 = FStar.Int8

(* `add_mod` wraps around modulo `pow2 n`. *)
let add_mod_wraps () : Lemma (U32.v (U32.add_mod 0xfffffffful 1ul) == 0) =
  assert_norm (pow2 32 == 0x100000000)

(* `add_underspec` is specified only when the sum fits. *)
let add_underspec_no_overflow () : Lemma (U8.v (U8.add_underspec 100uy 27uy) == 127) =
  assert_norm (pow2 8 == 256)

(* The checked `+` requires the sum to fit. *)
let checked_add (x:U8.t{U8.v x < 100}) : U8.t = U8.(x + 100uy)

(* Signed division truncates towards zero; the remainder has the sign of the dividend. *)
let signed_div_rem () : Lemma
  (I8.v (I8.div (I8.int_to_t (-7)) (I8.int_to_t 2)) == -3 /\
   I8.v (I8.rem (I8.int_to_t (-7)) (I8.int_to_t 2)) == -1) =
  assert_norm (FStar.Int.((-7) /- 2) == -3);
  assert_norm (FStar.Int.mod #8 (-7) 2 == -1);
  assert_norm (pow2 7 == 128)

(* A left shift by fewer than `n` bits. *)
let shift_left_example () : Lemma (U32.v (U32.shift_left 1ul 4ul) == 16) =
  FStar.UInt.shift_left_value_lemma #32 1 4;
  assert_norm (pow2 4 == 16);
  assert_norm (pow2 32 == 0x100000000)

(* `eq_mask` gives all ones on equal inputs and zero otherwise. *)
let eq_mask_example () : Lemma
  (U8.v (U8.eq_mask 3uy 3uy) == 255 /\ U8.v (U8.eq_mask 3uy 4uy) == 0) =
  assert_norm (pow2 8 == 256)
