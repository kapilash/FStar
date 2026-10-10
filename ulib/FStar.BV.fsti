(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FStar.BV

/// This module defines an abstract type of length-indexed bit
/// vectors.  The type and its operations are handled primitively in
/// F*'s SMT encoding, which maps them to the SMT sort of bit vectors
/// and operations on that sort. Note that this encoding only applies
/// when the length [n] is a syntactic literal: bit vectors with a
/// length referring to some variable, bound or otherwise, are encoded
/// as abstract sequences of bits.
///
/// Because of this syntactic encoding, it is also often helpful to
/// explicitly specify the bit length on all operations -- for example
/// constructing a 64-bit vector with [int2bv #64 1]. These explicit
/// annotations ensure that the encoding uses the literal length 64,
/// rather than inferring some variable as the length.
///
/// One way to use this module is in conjunction with
/// FStar.Tactics.BV. Its main tactic, [bv_tac], converts bitwise
/// operations on unsigned integers to operations on bit vectors and
/// back using the [int2bv / bv2int] isomorphism. This can be an
/// effective way of discharging such proof obligations for bitwise
/// operations on integers using the SMT solver's theory of
/// bitvectors.

open FStar.UInt
// for now just opening this for logand, logxor, etc. but we need a better solution.

(*| Bit vectors of length `n` for the SMT solver's bit-vector theory, with decidable equality.

    The type is abstract. When `n` is a syntactic literal, the SMT encoding maps `bv_t n` and the primitive operations of this module (`bvand`, `bvadd`, `bvshl`, `bvult`, `int2bv`, `bv2int` and so on) to the SMT-LIB bit-vector sort and functions, so Z3 reasons about them natively. A length that is a variable gets no such encoding, so give the length explicitly, as in `int2bv #64 1`, rather than letting it be inferred.

    This is different from `FStar.BitVector.bv_t`, the sequence-of-booleans model that this module uses as its implementation. Lemmas such as `FStar.BV.int2bv_logand` relate the operations to those of `FStar.UInt` on bounded integers.

    ```fstar
    let bvand_comm_32 (x y: FStar.BV.bv_t 32)
      : Lemma (FStar.BV.bvand x y == FStar.BV.bvand y x)
      = ()
    ``` *)
val bv_t (n: nat) : eqtype

(* Experimental:
   Redefining basic type from UInt to avoid importing UInt
   Reduces verification time by 50% in small examples
// let max_int (n:nat) : Tot int = pow2 n - 1
// let min_int (n:nat) : Tot int = 0
// let fits (x:int) (n:nat) : Tot bool = min_int n <= x && x <= max_int n
// let size (x:int) (n:nat) : Tot Type0 = b2t(fits x n)
// type uint_t' (n:nat) = x:int{size x n}
*)

(*| Zero-extends a vector of length `n` to length `m + n` by adding `m` zero bits at the most significant end.

    An SMT bit-vector primitive (`zero_extend`). See `FStar.BV.int2bv_bv_uext` for its integer meaning. *)
val bv_uext (#n #m: pos) (a: bv_t n) : Tot (bv_t (m + n))

(**** Relating unsigned integers to bitvectors *)

(*| Converts an unsigned integer below `pow2 n` to the length-`n` bit vector representing it.

    An SMT bit-vector primitive. Its inverse is `FStar.BV.bv2int`; see `FStar.BV.inverse_num_lemma` and `FStar.BV.inverse_vec_lemma`. *)
val int2bv (#n: pos) (num: uint_t n) : Tot (bv_t n)

(*| Converts a length-`n` bit vector to the unsigned integer below `pow2 n` that it represents.

    An SMT bit-vector primitive and the inverse of `FStar.BV.int2bv`. *)
val bv2int (#n: pos) (vec: bv_t n) : Tot (uint_t n)

(*| `int2bv` maps equal integers to equal vectors. *)
val int2bv_lemma_1 (#n: pos) (a b: uint_t n)
    : Lemma (requires a = b) (ensures (int2bv #n a = int2bv #n b))

(*| `int2bv` is injective: equal vectors come from equal integers. *)
val int2bv_lemma_2 (#n: pos) (a b: uint_t n)
    : Lemma (requires (int2bv a = int2bv b)) (ensures a = b)

(*| `int2bv (bv2int vec)` is `vec`.

    Triggered automatically on `int2bv (bv2int vec)`. *)
val inverse_vec_lemma (#n: pos) (vec: bv_t n)
    : Lemma (requires True) (ensures vec = (int2bv (bv2int vec))) [SMTPat (int2bv (bv2int vec))]

(*| `bv2int (int2bv num)` is `num`.

    Has an SMT pattern on `bv2int (int2bv num)`, but with a literal length the native bit-vector encoding of these terms can keep the pattern from helping; calling the lemma explicitly is reliable:

    ```fstar
    let int2bv_roundtrip (x: FStar.UInt.uint_t 16)
      : Lemma (FStar.BV.bv2int #16 (FStar.BV.int2bv #16 x) == x)
      = FStar.BV.inverse_num_lemma #16 x
    ``` *)
val inverse_num_lemma (#n: pos) (num: uint_t n)
    : Lemma (requires True)
      (ensures num = bv2int #n (int2bv #n num))
      [SMTPat (bv2int #n (int2bv #n num))]

(*| Zero-extending `int2bv a` by `i` bits gives the vector of `FStar.UInt.zero_extends i a`, the same integer at width `i + n`. *)
val int2bv_bv_uext (#n #i: pos)
  (a: uint_t n)
  : Lemma
    (ensures (bv_uext #n #i (int2bv #n a) == int2bv #(i + n) (zero_extends #n i a)))

(**** Relating lists to bitvectors *)

(*| Builds a bit vector from a list of booleans of length `n`, the head becoming index `0`.

    Not an SMT primitive; it goes through `FStar.Seq.Base.seq_of_list`. Inverse of `FStar.BV.bv2list`. *)
val list2bv (#n: pos) (l: list bool {List.length l = n}) : Tot (bv_t n)

(*| Lists the bits of a vector, from index `0`, as a list of booleans of length `n`.

    Inverse of `FStar.BV.list2bv`. *)
val bv2list: #n: pos -> bv_t n -> Tot (l: list bool {List.length l = n})

(*| `bv2list (list2bv a)` is `a`. Call it explicitly; it has no SMT pattern. *)
val list2bv_bij (#n: pos) (a: list bool {List.length a = n})
    : Lemma (requires (True)) (ensures (bv2list (list2bv #n a) = a))

(*| `list2bv (bv2list a)` is `a`. Call it explicitly; it has no SMT pattern. *)
val bv2list_bij (#n: pos) (a: bv_t n)
    : Lemma (requires (True)) (ensures (list2bv (bv2list #n a) = a))

(**** Bitwise logical operators *)

(*| Bitwise conjunction (SMT-LIB `bvand`). Corresponds to `FStar.UInt.logand`, see `FStar.BV.int2bv_logand`. *)
val bvand (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(*| Bridge lemma: if `bvand` applied to `int2bv x` and `int2bv y` equals `z`, then `int2bv (logand x y)` equals `z`.

    It moves the integer operation `logand` into the SMT bit-vector theory. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_logand:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvand #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (logand #n x y) == z)

(*| Bitwise exclusive or (SMT-LIB `bvxor`). Corresponds to `FStar.UInt.logxor`, see `FStar.BV.int2bv_logxor`. *)
val bvxor (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(*| Bridge lemma: if `bvxor` applied to `int2bv x` and `int2bv y` equals `z`, then `int2bv (logxor x y)` equals `z`.

    It moves the integer operation `logxor` into the SMT bit-vector theory. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_logxor:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvxor #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (logxor #n x y) == z)

(*| Bitwise disjunction (SMT-LIB `bvor`). Corresponds to `FStar.UInt.logor`, see `FStar.BV.int2bv_logor`. *)
val bvor (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(*| Bridge lemma: if `bvor` applied to `int2bv x` and `int2bv y` equals `z`, then `int2bv (logor x y)` equals `z`.

    It moves the integer operation `logor` into the SMT bit-vector theory. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_logor:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvor #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (logor #n x y) == z)

(*| Bitwise negation (SMT-LIB `bvnot`). Corresponds to `FStar.UInt.lognot`, see `FStar.BV.int2bv_lognot`. *)
val bvnot (#n: pos) (a: bv_t n) : Tot (bv_t n)

(*| Bridge lemma: if `bvnot (int2bv x)` equals `z`, then `int2bv (lognot x)` equals `z`.

    Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_lognot: #n: pos -> #x: uint_t n -> #z: bv_t n -> squash (bvnot #n (int2bv #n x) == z)
  -> Lemma (int2bv #n (lognot #n x) == z)

(*| Logical shift left by an amount given as a bit vector (SMT-LIB `bvshl`); zeroes fill the low-order bits.

    Maps directly to the SMT primitive, so it can be cheaper than `FStar.BV.bvshl`, which takes an unbounded integer amount that must be converted. Corresponds to `FStar.UInt.shift_left`, see `FStar.BV.int2bv_shl'`. *)
val bvshl' (#n: pos) (a: bv_t n) (s: bv_t n) : Tot (bv_t n)

(*| Logical shift left by an amount given as a natural number; zeroes fill the low-order bits.

    Kept for compatibility; `FStar.BV.bvshl'` takes the amount as a bit vector and maps directly to SMT-LIB `bvshl`. Corresponds to `FStar.UInt.shift_left`, see `FStar.BV.int2bv_shl`. *)
val bvshl  (#n: pos) (a: bv_t n) (s: nat)    : Tot (bv_t n)

(*| Bridge lemma: if `bvshl'` applied to `int2bv x` and `int2bv y` equals `z`, then `int2bv (shift_left x y)` equals `z`.

    It moves the integer operation `shift_left` into the SMT bit-vector theory. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_shl':
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvshl' #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (shift_left #n x y) == z)

(*| Bridge lemma: if `bvshl (int2bv x) y`, with the amount `y` given as an integer, equals `z`, then `int2bv (shift_left x y)` equals `z`.

    Variant of the primed lemma for the integer-amount operator `FStar.BV.bvshl`. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_shl:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvshl #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (shift_left #n x y) == z)

(*| Logical shift right by an amount given as a bit vector (SMT-LIB `bvlshr`); zeroes fill the high-order bits.

    Maps directly to the SMT primitive, so it can be cheaper than `FStar.BV.bvshr`, which takes an unbounded integer amount. Corresponds to `FStar.UInt.shift_right`, see `FStar.BV.int2bv_shr'`. *)
val bvshr' (#n: pos) (a: bv_t n) (s: bv_t n) : Tot (bv_t n)

(*| Logical shift right by an amount given as a natural number; zeroes fill the high-order bits.

    Kept for compatibility; see `FStar.BV.bvshr'`. Corresponds to `FStar.UInt.shift_right`, see `FStar.BV.int2bv_shr`. *)
val bvshr  (#n: pos) (a: bv_t n) (s: nat)    : Tot (bv_t n)

(*| Bridge lemma: if `bvshr'` applied to `int2bv x` and `int2bv y` equals `z`, then `int2bv (shift_right x y)` equals `z`.

    It moves the integer operation `shift_right` into the SMT bit-vector theory. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_shr':
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvshr' #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (shift_right #n x y) == z)

(*| Bridge lemma: if `bvshr (int2bv x) y`, with the amount `y` given as an integer, equals `z`, then `int2bv (shift_right x y)` equals `z`.

    Variant of the primed lemma for the integer-amount operator `FStar.BV.bvshr`. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_shr:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvshr #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (shift_right #n x y) == z)

(**** Rotate operations *)

(*| Rotate left by an amount given as a bit vector. Corresponds to `FStar.UInt.rotate_left`, see `FStar.BV.int2bv_rol'`. *)
val bvrol' (#n: pos) (a: bv_t n) (s: bv_t n) : Tot (bv_t n)

(*| Rotate left by an amount given as a natural number. See also `FStar.BV.bvrol'` and `FStar.BV.int2bv_rol`. *)
val bvrol  (#n: pos) (a: bv_t n) (s: nat)    : Tot (bv_t n)

(*| Bridge lemma: if `bvrol'` applied to `int2bv x` and `int2bv y` equals `z`, then `int2bv (rotate_left x y)` equals `z`.

    It moves the integer operation `rotate_left` into the SMT bit-vector theory. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_rol':
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvrol' #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (rotate_left #n x y) == z)

(*| Bridge lemma: if `bvrol (int2bv x) y`, with the amount `y` given as an integer, equals `z`, then `int2bv (rotate_left x y)` equals `z`.

    Variant of the primed lemma for the integer-amount operator `FStar.BV.bvrol`. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_rol:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvrol #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (rotate_left #n x y) == z)

(*| Rotate right by an amount given as a bit vector. Corresponds to `FStar.UInt.rotate_right`, see `FStar.BV.int2bv_ror'`. *)
val bvror' (#n: pos) (a: bv_t n) (s: bv_t n) : Tot (bv_t n)

(*| Rotate right by an amount given as a natural number. See also `FStar.BV.bvror'` and `FStar.BV.int2bv_ror`. *)
val bvror  (#n: pos) (a: bv_t n) (s: nat)    : Tot (bv_t n)

(*| Bridge lemma: if `bvror'` applied to `int2bv x` and `int2bv y` equals `z`, then `int2bv (rotate_right x y)` equals `z`.

    It moves the integer operation `rotate_right` into the SMT bit-vector theory. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_ror':
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvror' #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (rotate_right #n x y) == z)

(*| Bridge lemma: if `bvror (int2bv x) y`, with the amount `y` given as an integer, equals `z`, then `int2bv (rotate_right x y)` equals `z`.

    Variant of the primed lemma for the integer-amount operator `FStar.BV.bvror`. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_ror:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvror #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (rotate_right #n x y) == z)

(**** Arithmetic operations *)
(*| The all-zero bit vector of length `n`, an abbreviation for `int2bv #n 0`. *)
unfold
let bv_zero #n = int2bv #n 0

(*| Unsigned less-than on bit vectors (SMT-LIB `bvult`).

    Agrees with `<` on the integers they represent; see `FStar.BV.int2bv_lemma_ult_1` and `FStar.BV.int2bv_lemma_ult_2`. *)
val bvult (#n: pos) (a b: bv_t n) : Tot (bool)

(*| If `a < b` then `bvult (int2bv a) (int2bv b)`. *)
val int2bv_lemma_ult_1 (#n: pos) (a b: uint_t n)
    : Lemma (requires a < b) (ensures (bvult #n (int2bv #n a) (int2bv #n b)))

(*| If `bvult (int2bv a) (int2bv b)` then `a < b`. *)
val int2bv_lemma_ult_2 (#n: pos) (a b: uint_t n)
    : Lemma (requires (bvult #n (int2bv #n a) (int2bv #n b))) (ensures a < b)

(*| Addition modulo `pow2 n` (SMT-LIB `bvadd`). Corresponds to `FStar.UInt.add_mod`, see `FStar.BV.int2bv_add`. *)
val bvadd (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(*| Bridge lemma: if `bvadd` applied to `int2bv x` and `int2bv y` equals `z`, then `int2bv (add_mod x y)` equals `z`.

    It moves the integer operation `add_mod` into the SMT bit-vector theory. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_add:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvadd #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (add_mod #n x y) == z)

(*| Subtraction modulo `pow2 n` (SMT-LIB `bvsub`). Corresponds to `FStar.UInt.sub_mod`, see `FStar.BV.int2bv_sub`. *)
val bvsub (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(*| Bridge lemma: if `bvsub` applied to `int2bv x` and `int2bv y` equals `z`, then `int2bv (sub_mod x y)` equals `z`.

    It moves the integer operation `sub_mod` into the SMT bit-vector theory. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_sub:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvsub #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (sub_mod #n x y) == z)

(*| Unsigned division of a bit vector by a nonzero integer divisor (SMT-LIB `bvudiv`).

    Corresponds to `FStar.UInt.udiv`, see `FStar.BV.int2bv_div`. For a divisor given as a bit vector, see `FStar.BV.bvdiv_unsafe`. *)
val bvdiv (#n: pos) (a: bv_t n) (b: uint_t n {b <> 0}) : Tot (bv_t n)

(*| Bridge lemma: if `bvdiv (int2bv x) y`, for a nonzero `y`, equals `z`, then `int2bv (udiv x y)` equals `z`.

    Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_div:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n {y <> 0} ->
    #z: bv_t n ->
    squash (bvdiv #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (udiv #n x y) == z)


(*| Unsigned division of two bit vectors, mapped to SMT-LIB `bvudiv`, with no precondition on the divisor.

    Clients only know its value for a nonzero divisor, through `FStar.BV.bvdiv_unsafe_sound`; the result for a zero divisor is left unspecified by the interface. *)
val bvdiv_unsafe (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(*| When `bv2int b` is nonzero, `bvdiv_unsafe a b` equals `bvdiv a (bv2int b)`. *)
val bvdiv_unsafe_sound :
    #n: pos ->
    #a : bv_t n ->
    #b : bv_t n ->
    squash (bv2int b <> 0)
  -> Lemma (bvdiv_unsafe #n a b = bvdiv a (bv2int b))


(*| Unsigned remainder of a bit vector by a nonzero integer divisor (SMT-LIB `bvurem`).

    Corresponds to `FStar.UInt.mod`, see `FStar.BV.int2bv_mod`. For a divisor given as a bit vector, see `FStar.BV.bvmod_unsafe`. *)
val bvmod (#n: pos) (a: bv_t n) (b: uint_t n {b <> 0}) : Tot (bv_t n)

(*| Bridge lemma: if `bvmod (int2bv x) y`, for a nonzero `y`, equals `z`, then `int2bv (mod x y)` equals `z`.

    Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_mod:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n {y <> 0} ->
    #z: bv_t n ->
    squash (bvmod #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (mod #n x y) == z)

(*| Unsigned remainder of two bit vectors, mapped to SMT-LIB `bvurem`, with no precondition on the divisor.

    Clients only know its value for a nonzero divisor, through `FStar.BV.bvmod_unsafe_sound`; the result for a zero divisor is left unspecified by the interface. *)
val bvmod_unsafe (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(*| When `bv2int b` is nonzero, `bvmod_unsafe a b` equals `bvmod a (bv2int b)`. *)
val bvmod_unsafe_sound :
    #n: pos ->
    #a : bv_t n ->
    #b : bv_t n ->
    squash (bv2int b <> 0)
  -> Lemma (bvmod_unsafe #n a b = bvmod a (bv2int b))

(*| Multiplication modulo `pow2 n` of a bit vector by an integer (SMT-LIB `bvmul`).

    Corresponds to `FStar.UInt.mul_mod`, see `FStar.BV.int2bv_mul`. `FStar.BV.bvmul'` takes both operands as bit vectors. *)
val bvmul (#n: pos) (a: bv_t n) (b: uint_t n) : Tot (bv_t n)

(*| Bridge lemma: if `bvmul (int2bv x) y` equals `z`, then `int2bv (mul_mod x y)` equals `z`.

    Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_mul:
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvmul #n (int2bv #n x) y == z)
  -> Lemma (int2bv #n (mul_mod #n x y) == z)

(*| Multiplication modulo `pow2 n` of two bit vectors (SMT-LIB `bvmul`).

    Corresponds to `FStar.UInt.mul_mod`, see `FStar.BV.int2bv_mul'`. *)
val bvmul' (#n: pos) (a b: bv_t n) : Tot (bv_t n)

(*| Bridge lemma: if `bvmul'` applied to `int2bv x` and `int2bv y` equals `z`, then `int2bv (mul_mod x y)` equals `z`.

    It moves the integer operation `mul_mod` into the SMT bit-vector theory. Used by `FStar.Tactics.BV.bv_tac`; call it explicitly otherwise. *)
val int2bv_mul':
    #n: pos ->
    #x: uint_t n ->
    #y: uint_t n ->
    #z: bv_t n ->
    squash (bvmul' #n (int2bv #n x) (int2bv #n y) == z)
  -> Lemma (int2bv #n (mul_mod #n x y) == z)

