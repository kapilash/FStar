module DocsUlibTacDerived

(* Examples from the documentation of FStar.Tactics.V2.Derived,
   FStar.Tactics.V2.Logic and FStar.Tactics.Util *)

open FStar.Tactics.V2

let _ = assert (True /\ 1 + 1 == 2) by (split (); trivial (); trivial ())

let _ = assert (True /\ True) by (seq split trivial)

let _ = assert (forall (x:int). x > 0 ==> x >= 0)
          by (let _ = forall_intro () in
              let _ = implies_intro () in
              smt ())

let _ = assert (forall (p q : prop). p ==> q ==> p)
          by (let _ = l_intros () in
              assumption ())

let _ = assert (exists (n:nat). n > 2) by (witness (`3))

let _ = assert (False \/ True) by (right (); trivial ())

let double (x:int) : int = x + x
let double_eq (x:int) : Lemma (double x == x + x) = ()

let _ = assert (double 3 == 6) by (l_to_r [`double_eq]; trivial ())

let _ = assert (1 + 1 == 2 /\ 2 + 2 == 4)
          by (split (); iterAll (fun () -> trivial ()))

let _ = assert True by (let l = FStar.Tactics.Util.map (fun x -> x + 1) [1; 2] in
                        guard (l = [2; 3]))
