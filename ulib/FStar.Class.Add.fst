(*
   Copyright 2008-2023 Microsoft Research

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
module FStar.Class.Add

(*| Typeclass of additive structures on `a`: a value `zero` and a binary operation `plus`.

    Fields:

    - `zero`: the intended neutral element.
    - `plus`: the combining operation, also written `++` (`FStar.Class.Add.op_Plus_Plus`).

    Intended for monoids, but no laws are recorded: the class does not require `zero` to be neutral or `plus` to be associative. Instances exist for `int`, `bool` and `list`. A generic fold:

    ```fstar
    let sum (#a: Type) {| additive a |} (xs: list a) : a =
      FStar.List.Tot.Base.fold_right (++) xs zero
    ``` *)
class additive a = {
  zero       : a;
  plus       : a -> a -> a;
}

(*| Combines two values with the `plus` method of the `FStar.Class.Add.additive` instance in scope. *)
val (++) : #a:_ -> {| additive a |} -> a -> a -> a
let (++) = plus

(*| Integers under addition, with `zero = 0`. *)
instance add_int : additive int = {
  zero = 0;
  plus = (+);
}

(*| Booleans under disjunction, with `zero = false`. *)
instance add_bool : additive bool = {
  zero = false;
  plus = ( || );
}

(*| Lists under concatenation (`FStar.List.Tot.Base.append`), with `zero = []`. *)
instance add_list #a : additive (list a) = {
  zero = [];
  plus = List.Tot.Base.append;
}
