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
module FStar.Int.Cast.Full

include FStar.Int.Cast

module U64  = FStar.UInt64
module U128 = FStar.UInt128

(*| Converts a 64-bit unsigned integer to a 128-bit unsigned integer, preserving its value (zero extension).

    Total. The contract is `FStar.UInt128.v b == FStar.UInt64.v a`; implemented by `FStar.UInt128.uint64_to_uint128`. Marked `inline_for_extraction noextract`, so it is inlined at extraction rather than extracted as a definition. *)
inline_for_extraction noextract
val uint64_to_uint128: a:U64.t -> b:U128.t{U128.v b == U64.v a}
inline_for_extraction noextract
let uint64_to_uint128 a = U128.uint64_to_uint128 a

(*| Converts a 128-bit unsigned integer to a 64-bit unsigned integer by truncation, keeping the low 64 bits.

    Total. The contract is `FStar.UInt64.v b == FStar.UInt128.v a % pow2 64`; implemented by `FStar.UInt128.uint128_to_uint64`. Marked `inline_for_extraction noextract`, so it is inlined at extraction rather than extracted as a definition.

    ```fstar
    let widen_then_narrow (x:FStar.UInt64.t)
      : Lemma (FStar.Int.Cast.Full.uint128_to_uint64
                 (FStar.Int.Cast.Full.uint64_to_uint128 x) == x)
      = FStar.Math.Lemmas.small_mod (FStar.UInt64.v x) (pow2 64);
        FStar.UInt64.v_inj (FStar.Int.Cast.Full.uint128_to_uint64
                              (FStar.Int.Cast.Full.uint64_to_uint128 x)) x
    ``` *)
inline_for_extraction noextract
val uint128_to_uint64: a:U128.t -> b:U64.t{U64.v b == U128.v a % pow2 64}
inline_for_extraction noextract
let uint128_to_uint64 a = U128.uint128_to_uint64 a
