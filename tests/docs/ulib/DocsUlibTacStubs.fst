module DocsUlibTacStubs

(* Examples from the documentation of the tactic primitives and of
   FStar.Tactics.Effect, FStar.Tactics.Typeclasses and FStar.Tactics.Print *)

open FStar.Tactics.V2

let _ = assert (1 + 1 == 2) by (norm [primops]; trefl ())

let forty_two : int = _ by (exact (`42))

let id_int : int -> int = _ by (let x = intro () in exact (binding_to_term x))

let _ = assert (True /\ True) by (split (); trivial (); trivial ())

let recover () : Tac unit =
  match catch (fun () -> fail "boom") with
  | Inl _ -> trivial ()
  | Inr () -> trivial ()

let _ = assert True by (recover ())

let _ = assert (forall (x:int). x + 0 == x)
          by (let _ = forall_intro () in smt ())

class has_zero (a:Type) = { zero : a }

instance has_zero_int : has_zero int = { zero = 0 }

let z : int = zero

let z' : has_zero int = FStar.Tactics.Typeclasses.solve

[@@postprocess_with (fun () -> norm [delta_only [`%forty_two]]; trefl ())]
let fifty : int = forty_two + 8

let _ = assert True by (guard (term_to_ast_string (`1) = "C_Int 1"); trivial ())
