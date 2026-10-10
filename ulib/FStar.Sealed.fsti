(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: G. Martinez, N. Swamy
*)

module FStar.Sealed

(* This module provides the type ``sealed a`` which is a singleton
   type from the perspective of F*'s logic. I.e., two values `x, y`
   both of type `sealed a` are provably equal.

   However, from the meta-F*, i.e., using the Tac effect, one can
   break the seal and extract an underlying value of type `a` from a
   `sealed a`.

   See also FStar.Sealed.Inhabited for a version of this module for
   use with inhabited types, in a style that is more efficient for
   SMT-based reasoning
*)
(*| A value of type `a` hidden from the logic.

    Within the logic, `sealed a` is a singleton: any two values of this type
    are provably equal (see `FStar.Sealed.sealed_singl`). The hidden value can
    only be observed with `FStar.Sealed.unseal`, which has the
    nondeterministic `Nd` effect, for instance in metaprograms.

    See `FStar.Sealed.Inhabited` for a variant better suited to SMT reasoning
    about inhabited types. *)
assume
new type sealed ([@@@strictly_positive] a : Type u#aa) : Type u#0

(*| Any two sealed values of the same type are equal.

    This is the main axiom of the module. It is sound because the hidden value
    can only be observed through the nondeterministic `FStar.Sealed.unseal`. *)
val sealed_singl (#a:Type) (x y : sealed a)
  : Lemma (x == y)

(*| Hides a value, making it invisible to the logic. *)
val seal (#a : Type u#aa) (x:a) : Tot (sealed a)

(*| Observes the value hidden in a sealed value.

    The elimination form for `FStar.Sealed.sealed`. It is not a function: it
    has the `Nd` effect, so nothing is known about its result, and
    `FStar.Sealed.sealed_singl` cannot be used to prove that two values of type
    `a` are equal. `Nd` is a total effect and a sub-effect of `Tac`, so
    terminating programs and metaprograms can both unseal. *)
val unseal (#a : Type u#aa) (s : sealed a) : Nd a

(*| Applies a nondeterministic function to a sealed value, sealing the result. *)
val map_seal (#a : Type u#aa) (#b : Type u#bb) (s : sealed a) (f : a -> Nd b) : Tot (sealed b)

(*| Applies a nondeterministic function returning a sealed value to a sealed
    value. *)
val bind_seal (#a : Type u#aa) (#b : Type u#bb) (s : sealed a) (f : a -> Nd (sealed b)) : Tot (sealed b)
