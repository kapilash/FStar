(*
   Copyright 2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: N. Swamy
*)

module FStar.WellFounded.Util
open FStar.WellFounded
(** Provides some utilities related to well-founded relations *)

(* 1. Given a well-founded relation `r:binrel a`
      turn it into a well-founded relation on `binrel top`,
      by construction a relation that only relates `top` elements
      in `a` by `r`

      This is useful when writing type-polymorphic recursive functions
      whose termination depends on some custom well-founded order

      See tests/micro-benchmarks/TestWellFoundedRecursion.rel_poly2
*)

(*| The type of dependent pairs of a type and a value of that type.

    Used by `FStar.WellFounded.Util.lift_binrel` to state well-founded orders
    for type-polymorphic recursive functions. *)
let top = (b:Type & b)

(*| Lifts a relation `r` on `a` to a relation on `FStar.WellFounded.Util.top`
    that relates two pairs only when both carry the type `a` and their values
    are related by `r`.

    Well-foundedness is preserved, see
    `FStar.WellFounded.Util.lift_binrel_well_founded`. This is useful for
    type-polymorphic recursive functions whose termination depends on a custom
    well-founded order. *)
let lift_binrel (#a:Type)
                (r:binrel a)
    : binrel top
    = fun (t0 t1:top) ->
        dfst t0==a /\ dfst t1==a /\ r (dsnd t0) (dsnd t1)

(*| If `r y x`, then the lifted relation relates `(| a, y |)` and `(| a, x |)`. *)
val intro_lift_binrel (#a:Type) (r:binrel a) (y:a) (x:a)
  : Lemma
    (requires r y x)
    (ensures lift_binrel r (| a, y |) (| a, x |))

(*| If the lifted relation relates `y` to `(| a, x |)`, then `y` carries the
    type `a` and `r (dsnd y) x` holds. *)
val elim_lift_binrel (#a:Type) (r:binrel a) (y:top) (x:a)
  : Lemma
    (requires lift_binrel r y (| a, x |))
    (ensures dfst y == a /\ r (dsnd y) x)

(*| Extracts a proof of `r (dsnd x) (dsnd y)` from a proof that the lifted
    relation relates `x` and `y`. *)
val lower_binrel (#a:Type)
                 (#r:binrel a)
                 (x y:top)
                 (p:lift_binrel r x y)
  : r (dsnd x) (dsnd y)


(*| Lifting a well-founded relation with `FStar.WellFounded.Util.lift_binrel`
    gives a well-founded relation on `FStar.WellFounded.Util.top`. *)
val lift_binrel_well_founded (#a:Type u#a)
                             (#r:binrel u#a a)
                             (wf_r:well_founded r)
  : well_founded (lift_binrel r)

(*| The lifted relation `FStar.WellFounded.Util.lift_binrel r` packaged as a
    `FStar.WellFounded.well_founded_relation`, given that `r` is well-founded. *)
let lift_binrel_as_well_founded_relation (#a:Type u#a) (#r:binrel u#a a) (wf_r:well_founded r)
  : well_founded_relation u#(a + 1) (top u#a)
  = as_well_founded #top #(lift_binrel r) (lift_binrel_well_founded wf_r)
