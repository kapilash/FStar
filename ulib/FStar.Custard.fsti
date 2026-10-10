module FStar.Custard

(** Custard: pass [x] at run time instead of specializing on it.

    A [@@monomorphize] binder normally demands an argument whose value is
    known at specialization time.  Wrapping a call site's argument in [dyn]
    says the opposite: do not specialize on this one, emit a single version
    and pass the value at run time.  In the terms of doc/ref/custard.md
    section 3.2c this selects the *identity skeleton*, which is to say
    ordinary dictionary passing; it is the analogue of Rust's [dyn], and it
    exists for the same reason, to stop monomorphization where its cost
    outweighs its benefit.

    The opt-in is at the call site because that is where the knowledge lives:
    the callee may well be worth specializing everywhere else.

    [dyn] carries the [no_specialize] attribute, and Custard passes
    [DontUnfoldAttr] for it in every normalization it performs, so the
    marker survives the reduction that computes a specialization key.  That
    is the whole trick: [id x] would be normalized away to [x], leaving a
    bare variable and the rejection it triggers, whereas [dyn x] survives,
    [x] becomes a hole, and the argument abstracts to [fun v -> dyn v] --
    the identity skeleton.  Custard then compiles [dyn] itself away.

    Blocking the normalizer would normally cost the caller the knowledge
    that [dyn] is the identity, so the *specification* carries it instead:
    proofs and the SMT encoding see through [dyn] even where the normalizer
    is not allowed to. *)

(*| The attribute that Custard never unfolds during specialization; see `FStar.Custard.dyn`. *)
val no_specialize : unit

(*| Marks an argument that Custard should pass at run time instead of specializing on it.

    Logically `dyn x` is `x`: its postcondition is `r == x`, so proofs and the
    SMT encoding see through it. Because it carries the
    `FStar.Custard.no_specialize` attribute, the normalizer does not unfold it
    while computing specialization keys, so the argument becomes a hole and the
    callee is compiled once with the value passed at run time (ordinary
    dictionary passing). Custard then compiles `dyn` itself away. *)
[@@ no_specialize]
val dyn (#a:Type) (x:a) : Pure a (requires True) (ensures fun r -> r == x)
