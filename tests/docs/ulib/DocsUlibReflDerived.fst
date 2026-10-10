module DocsUlibReflDerived

(* Checked examples for the derived reflection and named-view modules:
   FStar.Reflection.V2.Derived, FStar.Reflection.V2.Formula,
   FStar.Reflection.V2.Compare, FStar.Tactics.NamedView and
   FStar.Tactics.V2.SyntaxHelpers. *)

open FStar.Tactics.V2

let _ = assert (1 + 1 == 2) by (
  match term_as_formula (cur_goal ()) with
  | Comp (Eq _) _ _ -> trivial ()
  | _ -> fail "expected an equality")

let _ = assert True by (
  match inspect (`(fun (x:int) -> x)) with
  | Tv_Abs b body -> guard (Tv_Var? (inspect body))
  | _ -> fail "expected an abstraction")

let _ = assert True by (
  let hd, args = collect_app (`(1 + 2)) in
  guard (List.Tot.length args = 2);
  guard (is_fvar hd (implode_qn add_qn)))

let sum12 : term = mk_e_app (pack (Tv_FVar (pack_fv add_qn))) [`1; `2]

let _ = assert True by (
  guard (compare_term sum12 (`(1 + 2)) = FStar.Order.Eq))
