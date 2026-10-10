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
module FStar.Algebra.CommMonoid


(*| A commutative monoid on `a`, whose laws hold up to propositional equality `==`.

    The single constructor `CM` has the fields:

    - `unit`: the neutral element.
    - `mult`: the binary operation.
    - `identity`: a proof that `mult unit x == x` (left identity).
    - `associativity`: a proof that `mult (mult x y) z == mult x (mult y z)`.
    - `commutativity`: a proof that `mult x y == mult y x`.

    Right identity follows; see `FStar.Algebra.CommMonoid.right_identity`.
    For laws up to a custom equivalence relation, use
    `FStar.Algebra.CommMonoid.Equiv.cm`, which the fold and matrix libraries
    are built on. A new instance discharges each law, often trivially:

    ```fstar
    let max_nat (x y: nat) : nat = if x >= y then x else y

    let max_nat_cm : cm nat =
      CM #nat 0 max_nat (fun _ -> ()) (fun _ _ _ -> ()) (fun _ _ -> ())
    ``` *)
unopteq
type cm (a:Type) =
  | CM :
    unit:a ->
    mult:(a -> a -> a) ->
    identity : (x:a -> Lemma (unit `mult` x == x)) ->
    associativity : (x:a -> y:a -> z:a ->
                      Lemma (x `mult` y `mult` z == x `mult` (y `mult` z))) ->
    commutativity:(x:a -> y:a -> Lemma (x `mult` y == y `mult` x)) ->
    cm a

(*| Proves that the unit of `m` is also a right identity: `mult x unit == x`.

    Derived from the `identity` and `commutativity` fields of `m`; call it
    explicitly. *)
let right_identity (#a:Type) (m:cm a) (x:a) :
    Lemma (CM?.mult m x (CM?.unit m) == x) =
  CM?.commutativity m x (CM?.unit m); CM?.identity m x

(*| The commutative monoid of integers under addition, with unit `0`.

    `FStar.Algebra.CommMonoid.Equiv.int_plus_cm` is the same monoid for the
    equivalence-based structure. *)
let int_plus_cm : cm int =
  CM 0 (+) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())

(*| The commutative monoid of integers under multiplication, with unit `1`.

    `FStar.Algebra.CommMonoid.Equiv.int_multiply_cm` is the same monoid for the
    equivalence-based structure. *)
let int_multiply_cm : cm int =
  CM 1 ( * ) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())
