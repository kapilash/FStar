module DocsUlibReflStubs

(* Examples from the documentation of FStar.Stubs.Reflection.V2.Builtins,
   FStar.Stubs.Reflection.V2.Data, FStar.Reflection.Const and
   FStar.Reflection.TermEq.Simple *)

open FStar.Tactics.V2
open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Reflection.Const
open FStar.Reflection.TermEq.Simple

let is_fvar_named (t:term) (qn:name) : bool =
  match inspect_ln t with
  | Tv_FVar fv -> inspect_fv fv = qn
  | _ -> false

let _ = assert True by (guard (is_fvar_named (`Prims.int) int_lid))

let unit_tm : term = pack_ln (Tv_Const C_Unit)

let _ = assert True by (guard (term_eq unit_tm (`())))

let _ = assert True by (guard (term_eq (`(1 + 2)) (`(1 + 2))))

let _ = assert_norm (is_tot_comp (mk_tot_comp (`int)))
