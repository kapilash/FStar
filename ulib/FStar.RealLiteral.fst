(*
   Copyright 2008-2025 Microsoft Research

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
module FStar.RealLiteral

(* Note: this module deliberately depends on nothing but Prims, since it is
referenced by the (very low-level) reflection API. Parsing a literal from a
string is in FStar.RealLiteral.Parse. *)

(*| Raw representation of a decimal real literal, denoting the exact rational number `mantissa * 10^exponent`.

    A record with two `int` fields, `mantissa` and `exponent`, with decidable equality. Literals are values of its canonical subset `FStar.RealLiteral.real_literal`. Its attributes `PpxDerivingYoJson` and `PpxDerivingShow` request derived JSON and `show` printers in extracted OCaml. *)
[@@ FStar.Attributes.PpxDerivingYoJson; FStar.Attributes.PpxDerivingShow]
type real_literal_repr = {
  mantissa : int;
  exponent : int;
}

(*| Holds when a literal uses no more decimal places than needed: either the exponent is 0, or it is negative and the last digit of the mantissa is non-zero.

    A positive exponent is never canonical. Every number denoted by some literal is denoted by exactly one canonical literal. *)
let canonical (r : real_literal_repr) : bool =
  r.exponent = 0 || (r.exponent < 0 && r.mantissa % 10 <> 0)

(*| Canonical decimal real literals: `FStar.RealLiteral.real_literal_repr` values satisfying `FStar.RealLiteral.canonical`.

    This is the type used by the F\* compiler for the real constants appearing in terms (`FStarC.Real.real`, the payload of `FStarC.Const.Const_real`) and the payload of the `C_Real` case of the reflection API's `vconst` type. It is the type of literals denoting reals, not of reals themselves (`FStar.Real.real`).

    Because the representation is canonical, two literals denote the same real number exactly when they are equal, so `=` on this type is decidable equality of the denoted numbers. This is essential for soundness: the F\* normalizer and the SMT solver both consider two real constants equal exactly when they denote the same number. Build values with `FStar.RealLiteral.mk`, `FStar.RealLiteral.of_int` or `FStar.RealLiteral.Parse.of_string`. *)
[@@ FStar.Attributes.PpxDerivingYoJson; FStar.Attributes.PpxDerivingShow]
type real_literal = r:real_literal_repr{canonical r}

private let rec pow10 (n : nat) : Tot pos = if n = 0 then 1 else 10 * pow10 (n-1)

(* Drops the trailing zeros of the mantissa, adjusting the exponent, so
that the result is canonical. *)
private let rec strip (m : int) (e : int{e <= 0}) : Tot real_literal (decreases (-e)) =
  if e = 0 || m % 10 <> 0
  then { mantissa = m; exponent = e }
  else strip (m / 10) (e + 1)

(*| Returns the canonical literal denoting `m * 10^e`.

    A non-negative exponent is folded into the mantissa; for a negative exponent, trailing zeros of the mantissa are removed.

    ```fstar
    let _ = assert_norm (FStar.RealLiteral.mk 150 (-2) == FStar.RealLiteral.mk 15 (-1))
    ``` *)
let mk (m e : int) : real_literal =
  if e >= 0
  then { mantissa = m * pow10 e; exponent = 0 }
  else strip m e

(*| Returns the literal denoting the integer `i` exactly (exponent 0). *)
let of_int (i : int) : real_literal = { mantissa = i; exponent = 0 }

(* The number of decimal digits of [x]. *)
private let rec ndigits (x : nat) : Tot nat (decreases x) =
  if x < 10 then 1 else 1 + ndigits (x / 10)

(* Prepends [n] zeros to [s]. *)
private let rec zeros (n : nat) (s : string) : Tot string (decreases n) =
  if n = 0 then s else zeros (n-1) ("0" ^ s)

(*| Returns a decimal representation of a literal, such as `"0.5"`, `"-1.5"` or `"10.0"`.

    The result always contains a `.` and is accepted by `FStar.RealLiteral.Parse.of_string`, which maps it back to the same literal (not proved in the library).

    ```fstar
    let _ = assert_norm (FStar.RealLiteral.to_string (FStar.RealLiteral.mk 15 (-1)) == "1.5")
    ``` *)
let to_string (r : real_literal) : string =
  let m = if r.mantissa < 0 then - r.mantissa else r.mantissa in
  let k : nat = - r.exponent in
  let p = pow10 k in
  let fpart = m % p in
  (* [fpart] must be printed with exactly [k] digits, zero-padded. *)
  let pad = if ndigits fpart >= k then 0 else k - ndigits fpart in
  (if r.mantissa < 0 then "-" else "")
    ^ string_of_int (m / p)
    ^ "."
    ^ (if k = 0 then "0" else zeros pad (string_of_int fpart))

(*| Compares the numbers denoted by two literals, returning `-1`, `0` or `1` when the first is respectively smaller than, equal to, or greater than the second. *)
let compare (r1 r2 : real_literal) : int =
  (* Scale both mantissas to the smaller of the two exponents. *)
  let e = if r1.exponent <= r2.exponent then r1.exponent else r2.exponent in
  let m1 = r1.mantissa * pow10 (r1.exponent - e) in
  let m2 = r2.mantissa * pow10 (r2.exponent - e) in
  if m1 < m2 then -1 else if m1 = m2 then 0 else 1
