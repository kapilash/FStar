module FStar.Pure.BreakVC

(* With the simplified pre/postcondition-based effect system, the
   specification of a computation is just a precondition and a
   postcondition; there is no way to express a computation that wraps its
   continuation's verification condition in [spinoff].  [break_vc] is
   therefore a no-op, kept only for source compatibility. *)
(*| Does nothing; kept only for source compatibility.

    It previously split the verification condition of its continuation into a
    separate query. With the current pre- and postcondition based effect
    system, this cannot be expressed. *)
val break_vc (_:unit) : Pure unit (requires True) (ensures fun _ -> True)
