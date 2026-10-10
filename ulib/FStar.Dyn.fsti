(*
   Copyright 2008-2024 Microsoft Research

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

module FStar.Dyn

/// Dynamic casts

(*| The type of dynamically typed values: a value of any type, packed with `FStar.Dyn.mkdyn` and recovered with `FStar.Dyn.undyn`.

    It lives in `Type0` whatever the universe of the packed value. Equality is
    not decidable. *)
val dyn : Type0

(*| Holds when `d` was created by `FStar.Dyn.mkdyn` from a value of type `a`.

    This is what makes `FStar.Dyn.undyn` safe: casting back is allowed only at
    the type the value was packed with. *)
val dyn_has_ty (d: dyn) (a: Type u#a) : prop

(*| Packs a value of any type into `dyn`, recording its type in the refinement `dyn_has_ty d a`.

    ```fstar
    let packed = FStar.Dyn.mkdyn #int 42

    let unpacked () : Dv int = FStar.Dyn.undyn #int packed
    ``` *)
val mkdyn (#a: Type u#a) (x: a) : d:dyn { dyn_has_ty d a }

(*| Casts a `dyn` back to the type it was packed with; requires `dyn_has_ty d a`.

    In the `Dv` effect. Nothing states that `undyn (mkdyn x)` returns `x`. The
    reference implementation in `FStar.Dyn.fst` shows the API can be realized
    safely; the OCaml realization is instead a handwritten unchecked cast. *)
val undyn (#a: Type u#a) (d: dyn { dyn_has_ty d a }) : Dv a
