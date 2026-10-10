module DocsUlibOrder

(* Examples from the documentation of FStar.Order, FStar.WellFounded,
   FStar.WellFoundedRelation, FStar.ReflexiveTransitiveClosure and FStar.GhostSet *)

let compare_pair (p q: int & int) : FStar.Order.order =
  let open FStar.Order in
  lex (compare_int (fst p) (fst q)) (fun _ -> compare_int (snd p) (snd q))

let _ = assert_norm (compare_pair (1, 5) (1, 3) == FStar.Order.Gt)

let lt_nat : FStar.WellFounded.binrel nat = fun x y -> x < y

let rec lt_nat_acc (n:nat) : Tot (FStar.WellFounded.acc lt_nat n) (decreases n) =
  FStar.WellFounded.AccIntro (fun m _ -> lt_nat_acc m)

let sum_to (n:nat) : nat =
  FStar.WellFounded.fix lt_nat_acc (fun _ -> nat)
    (fun n rec_call -> if n = 0 then 0 else n + rec_call (n - 1) ())
    n

let nat_nat_wfr = FStar.WellFoundedRelation.(lex_nondep_wfr (default_wfr nat) (default_wfr nat))

let rec count (x y: nat) : Tot nat (decreases (nat_nat_wfr.decreaser (x, y))) =
  if x = 0 then 0
  else if y = 0 then count (x - 1) 100
  else 1 + count x (y - 1)

let incr_step (x y: int) : prop = y == x + 1

let incr_closure_monotone (x y: int)
  : Lemma (requires FStar.ReflexiveTransitiveClosure.closure incr_step x y)
          (ensures x <= y) =
  FStar.ReflexiveTransitiveClosure.stable_on_closure incr_step (fun z -> x <= z) ()

let ghost_set_example (x y: int) =
  let open FStar.GhostSet in
  let s = union (singleton x) (singleton y) in
  assert (mem x s /\ mem y s);
  assert (subset (singleton x) s)
