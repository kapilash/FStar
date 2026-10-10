module FStar.Tactics.MApply0

open FStar.Stubs.Reflection.Types
open FStar.Tactics.Effect

(* Used by mapply, must be exposed, but not to be used directly *)
private val push1 : (#p:prop) -> (#q:prop) ->
                        squash (p ==> q) ->
                        squash p ->
                        squash q
private val push1' : (#p:prop) -> (#q:prop) ->
                         squash (p ==> q) ->
                         squash p ->
                         squash q

(* `m` is for `magic` *)
(*| Applies the term `t` to solve the current goal, trying several strategies; usually called through `FStar.Tactics.MApply.mapply`.

    It first tries `FStar.Tactics.V2.Derived.apply` and then
    `FStar.Tactics.V2.Derived.apply_lemma`. If both fail and `t` is a total
    function whose (possibly squashed) result is an implication `p ==> q`, it
    splits off the implication and retries, up to a fixed depth; otherwise it
    falls back to `apply`. Fails if none of these succeed. The `m` stands for
    "magic". *)
[@@plugin]
val mapply0 (t : term) : Tac unit
