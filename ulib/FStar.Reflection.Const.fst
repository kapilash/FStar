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
module FStar.Reflection.Const

(* Common lids *)

// TODO: these are awful names
// TODO: _qn vs _lid

(*| The fully qualified name of logical implication, `Prims.l_imp`.

    Like the other names in this module, it is used by metaprograms to
    recognise or build applications of a known symbol, by comparing with the
    result of `FStar.Stubs.Reflection.V2.Builtins.inspect_fv` or by passing
    it to `FStar.Stubs.Reflection.V2.Builtins.pack_fv`. *)
let imp_qn       = ["Prims"; "l_imp"]
(*| The fully qualified name of propositional conjunction, `Prims.l_and`. *)
let and_qn       = ["Prims"; "l_and"]
(*| The fully qualified name of propositional disjunction, `Prims.l_or`. *)
let or_qn        = ["Prims"; "l_or"]
(*| The fully qualified name of propositional negation, `Prims.l_not`. *)
let not_qn       = ["Prims"; "l_not"]
(*| The fully qualified name of logical equivalence, `Prims.l_iff`. *)
let iff_qn       = ["Prims"; "l_iff"]
(*| The fully qualified name of homogeneous propositional equality, `Prims.eq2`. *)
let eq2_qn       = ["Prims"; "eq2"]
(*| The name `Prims.eq`, which `FStar.Reflection.V2.Formula` treats as boolean equality.

    `Prims` currently defines no `eq`: boolean equality is `Prims.( = )`
    (internally `Prims.op_Equals`), so terms built with this name do not
    typecheck and inspected terms never match it. Kept for compatibility. *)
let eq1_qn       = ["Prims"; "eq"]
(*| The fully qualified name of the true proposition, `Prims.l_True`. *)
let true_qn      = ["Prims"; "l_True"]
(*| The fully qualified name of the false proposition, `Prims.l_False`. *)
let false_qn     = ["Prims"; "l_False"]
(*| The fully qualified name of the coercion from booleans to propositions, `Prims.b2t`. *)
let b2t_qn       = ["Prims"; "b2t"]
(*| The fully qualified name of universal quantification, `Prims.l_Forall`. *)
let forall_qn    = ["Prims"; "l_Forall"]
(*| The fully qualified name of existential quantification, `Prims.l_Exists`. *)
let exists_qn    = ["Prims"; "l_Exists"]
(*| The fully qualified name of `Prims.squash`. *)
let squash_qn    = ["Prims"; "squash"]
(*| The fully qualified name of the type of propositions, `Prims.prop`. *)
let prop_qn      = ["Prims"; "prop"]

(*| The fully qualified name of the boolean constructor `Prims.true`. *)
let bool_true_qn  = ["Prims"; "true"]
(*| The fully qualified name of the boolean constructor `Prims.false`. *)
let bool_false_qn = ["Prims"; "false"]

(*| The fully qualified name of the type `Prims.int`.

    Fully qualified names are lists of components, so `int_lid` is `["Prims"; "int"]`.

    ```fstar
    let is_fvar_named (t:term) (qn:name) : bool =
      match inspect_ln t with
      | Tv_FVar fv -> inspect_fv fv = qn
      | _ -> false

    let _ = assert True by (guard (is_fvar_named (`Prims.int) int_lid))
    ``` *)
let int_lid      = ["Prims"; "int"]
(*| The fully qualified name of the type `Prims.bool`. *)
let bool_lid     = ["Prims"; "bool"]
(*| The fully qualified name of the type `Prims.unit`. *)
let unit_lid     = ["Prims"; "unit"]
(*| The fully qualified name of the type `Prims.string`. *)
let string_lid   = ["Prims"; "string"]

(*| The fully qualified name of integer addition, `Prims.( + )` (internally `op_Plus`). *)
let add_qn       = ["Prims"; "op_Plus"]
(*| The fully qualified name of integer negation, `Prims.( ~- )` (internally `op_Tilde_Minus`). *)
let neg_qn       = ["Prims"; "op_Tilde_Minus"]
(*| The fully qualified name of integer subtraction, `Prims.( - )` (internally `op_Minus`). *)
let minus_qn     = ["Prims"; "op_Minus"]
(*| The fully qualified name of integer multiplication, `Prims.( * )` (internally `op_Star`). *)
let mult_qn      = ["Prims"; "op_Star"]
(*| The fully qualified name of integer division, `Prims.( / )` (internally `op_Slash`). *)
let div_qn       = ["Prims"; "op_Slash"]
(*| The fully qualified name of the integer comparison `Prims.( < )` (internally `op_Less`). *)
let lt_qn        = ["Prims"; "op_Less"]
(*| The fully qualified name of the integer comparison `Prims.( <= )` (internally `op_Less_Equals`). *)
let lte_qn       = ["Prims"; "op_Less_Equals"]
(*| The fully qualified name of the integer comparison `Prims.( > )` (internally `op_Greater`). *)
let gt_qn        = ["Prims"; "op_Greater"]
(*| The fully qualified name of the integer comparison `Prims.( >= )` (internally `op_Greater_Equals`). *)
let gte_qn       = ["Prims"; "op_Greater_Equals"]
(*| The fully qualified name of integer modulus, `Prims.( % )` (internally `op_Percent`). *)
let mod_qn       = ["Prims"; "op_Percent"]

(*| The fully qualified name of the list constructor `Prims.Nil`. *)
let nil_qn       = ["Prims"; "Nil"]
(*| The fully qualified name of the list constructor `Prims.Cons`. *)
let cons_qn      = ["Prims"; "Cons"]

(*| The fully qualified name of the pair constructor `FStar.Pervasives.Native.Mktuple2`. *)
let mktuple2_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple2"]
(*| The fully qualified name of the triple constructor `FStar.Pervasives.Native.Mktuple3`. *)
let mktuple3_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple3"]
(*| The fully qualified name of the 4-tuple constructor `FStar.Pervasives.Native.Mktuple4`. *)
let mktuple4_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple4"]
(*| The fully qualified name of the 5-tuple constructor `FStar.Pervasives.Native.Mktuple5`. *)
let mktuple5_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple5"]
(*| The fully qualified name of the 6-tuple constructor `FStar.Pervasives.Native.Mktuple6`. *)
let mktuple6_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple6"]
(*| The fully qualified name of the 7-tuple constructor `FStar.Pervasives.Native.Mktuple7`. *)
let mktuple7_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple7"]
(*| The fully qualified name of the 8-tuple constructor `FStar.Pervasives.Native.Mktuple8`. *)
let mktuple8_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple8"]

(*| The fully qualified name of bitwise and on machine integers, `FStar.UInt.logand`. *)
let land_qn    = ["FStar" ; "UInt" ; "logand"]
(*| The fully qualified name of bitwise exclusive or on machine integers, `FStar.UInt.logxor`. *)
let lxor_qn    = ["FStar" ; "UInt" ; "logxor"]
(*| The fully qualified name of bitwise or on machine integers, `FStar.UInt.logor`. *)
let lor_qn     = ["FStar" ; "UInt" ; "logor"]
(*| The fully qualified name of modular addition on machine integers, `FStar.UInt.add_mod`. *)
let ladd_qn    = ["FStar" ; "UInt" ; "add_mod"]
(*| The fully qualified name of modular subtraction on machine integers, `FStar.UInt.sub_mod`. *)
let lsub_qn    = ["FStar" ; "UInt" ; "sub_mod"]
(*| The fully qualified name of left shift on machine integers, `FStar.UInt.shift_left`. *)
let shiftl_qn  = ["FStar" ; "UInt" ; "shift_left"]
(*| The fully qualified name of right shift on machine integers, `FStar.UInt.shift_right`. *)
let shiftr_qn  = ["FStar" ; "UInt" ; "shift_right"]
(*| The fully qualified name of division on machine integers, `FStar.UInt.udiv`. *)
let udiv_qn    = ["FStar" ; "UInt" ; "udiv"]
(*| The fully qualified name of modulus on machine integers, `FStar.UInt.mod`. *)
let umod_qn    = ["FStar" ; "UInt" ; "mod"]
(*| The fully qualified name of modular multiplication on machine integers, `FStar.UInt.mul_mod`. *)
let mul_mod_qn = ["FStar" ; "UInt" ; "mul_mod"]
(*| The fully qualified name of the conversion from natural numbers to bit vectors, `FStar.BV.int2bv`. *)
let nat_bv_qn  = ["FStar" ; "BV"   ; "int2bv"]
