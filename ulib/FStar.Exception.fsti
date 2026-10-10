module FStar.Exception

(*| Returns a printable description of an exception.

    An uninterpreted primitive: it does not reduce in the normalizer and nothing
    is specified about the result. It is extracted to OCaml's
    `Printexc.to_string`, and it can also be used from tactic plugins. *)
val string_of_exn : exn -> string
