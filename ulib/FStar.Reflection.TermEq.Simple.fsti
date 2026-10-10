module FStar.Reflection.TermEq.Simple

(* This is just a wrapper over FStar.Reflection.TermEq.

For clients who just want to use term_eq, and not term_eq_dec, this
interface brings in less dependencies.

Returning just a boolean and providing the SMTPat lemma makes it a bit
more convenient to use: one can write `if term_eq (foo _) _` for an
effectful foo without running into a variable escaping its scope. *)

open FStar.Stubs.Reflection.Types
open FStar.Reflection.TermSpec

(*| Conservatively compares two terms: returns `true` only if they have the same denotation.

    The same function as `FStar.Reflection.TermEq.term_eq`, with the
    correctness property moved to the lemma
    `FStar.Reflection.TermEq.Simple.term_eq_ok` and fewer dependencies. A
    plain boolean result lets one write `if term_eq (f ()) t` with an effectful
    `f` without a variable escaping its scope. The denotation
    (`FStar.Reflection.TermSpec.denote_term`) ignores ranges, pretty-printing
    names and sealed sorts. Runs natively as a plugin.

    ```fstar
    let _ = assert True by (guard (term_eq (`(1 + 2)) (`(1 + 2))))
    ``` *)
[@@plugin]
val term_eq (t1 t2 : term) : bool

(*| If `FStar.Reflection.TermEq.Simple.term_eq t1 t2` returns `true`, then `t1` and `t2` have the same denotation.

    Triggered automatically on `term_eq t1 t2`. *)
val term_eq_ok (t1 t2 : term)
  : Lemma (requires term_eq t1 t2)
          (ensures denote_term t1 == denote_term t2)
          [SMTPat (term_eq t1 t2)]

(*| Conservatively compares two universes: returns `true` only if they are equal.

    The same function as `FStar.Reflection.TermEq.univ_eq`, with the
    correctness property moved to the lemma
    `FStar.Reflection.TermEq.Simple.univ_eq_ok`. Runs natively as a plugin. *)
[@@plugin]
val univ_eq (u1 u2 : universe) : bool

(*| If `FStar.Reflection.TermEq.Simple.univ_eq u1 u2` returns `true`, then `u1` and `u2` are equal.

    Triggered automatically on `univ_eq u1 u2`. *)
val univ_eq_ok (u1 u2 : universe)
  : Lemma (requires univ_eq u1 u2)
          (ensures u1 == u2)
          [SMTPat (univ_eq u1 u2)]
