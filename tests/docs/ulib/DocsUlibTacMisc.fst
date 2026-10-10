module DocsUlibTacMisc

open FStar.Tactics.V2
open FStar.Tactics.PatternMatching

let simplify_example (p:prop) =
  assert (True /\ (p \/ False) ==> p)
    by (FStar.Tactics.Simplifier.simplify ();
        let _ = FStar.Tactics.V2.implies_intro () in
        FStar.Tactics.V2.smt ())

let gpm_example (p q:prop) =
  assert (p ==> q ==> p)
    by (let _ = implies_intro () in
        let _ = implies_intro () in
        gpm (fun (a: prop) (h: hyp a) (g: pm_goal (squash a)) ->
               exact_hyp a h <: Tac unit) ())

let mapply_example (p q:prop) (lem:unit -> Lemma (p ==> q)) (hp:squash p) : squash q =
  _ by (FStar.Tactics.MApply.mapply (quote lem);
        FStar.Tactics.MApply.mapply (quote hp))

let smt_sync_example (x:int) =
  assert (x + 0 == x) by (FStar.Tactics.SMT.set_fuel 0;
                          FStar.Tactics.SMT.smt_sync ())

let lax_example () =
  assert True by guard (FStar.Tactics.LaxTermEq.lax_term_eq (`(fun x -> x + 1)) (`(fun y -> y + 1)))

let easy_example : x:nat -> Lemma (x + 0 == x) = FStar.Tactics.Easy.easy
