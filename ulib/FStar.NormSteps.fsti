[@@"no_prelude"]
module FStar.NormSteps

open Prims

(*| A normalization step: the steps passed to `FStar.Pervasives.norm`,
    `FStar.Pervasives.norm_spec` and normalization tactics control how terms
    are reduced. *)
val norm_step : Type0

(*| Logical simplification, for example rewriting `p /\ True` to `p`. *)
val simplify : norm_step

(*| Weak reduction: do not reduce under binders. *)
val weak : norm_step

(*| Head normal form: do not reduce in function arguments or in binder types. *)
val hnf : norm_step

(*| Reduce primitive operators, for example `1 + 1` to `2`. *)
val primops : norm_step

(*| Unfold all non-recursive definitions.

    To unfold only some definitions, see `FStar.NormSteps.delta_only`,
    `FStar.NormSteps.delta_attr`, `FStar.NormSteps.delta_qualifier` and
    `FStar.NormSteps.delta_namespace`. *)
val delta : norm_step

(*| Turn on debugging output for this normalization call. *)
val norm_debug : norm_step

(*| Unroll recursive calls.

    Termination checking is semantic rather than syntactic, so unrolling
    recursive calls in inconsistent contexts or on open terms can diverge. To
    avoid some trivial loops, `zeta` is disabled when reducing beneath a
    blocked match, so terms may not reduce as much as expected; see
    `FStar.NormSteps.zeta_full`. *)
val zeta : norm_step

(*| Unroll recursive calls as much as possible, without the loop-prevention
    heuristic of `FStar.NormSteps.zeta`.

    May loop; use with care. Implies `FStar.NormSteps.zeta`. *)
val zeta_full : norm_step

(*| Reduce case analysis: a `match` on a constructor application. *)
val iota : norm_step

(*| Use normalization by evaluation instead of interpretation. Experimental. *)
val nbe : norm_step

(*| Reify effectful definitions into their representations. *)
val reify_ : norm_step

(*| Unfold only the definitions named in the list.

    Each string is a fully qualified name, typically obtained with a `%`
    quotation; see `FStar.NormSteps.delta_fully` for an example. *)
val delta_only (s: list string) : Tot norm_step

(*| Unfold only the definitions named in the list, and each of them only once.

    Useful for a controlled unfolding of recursive definitions. When a name
    occurs several times, which occurrence is unfolded is unspecified. *)
val delta_once (s: list string) : Tot norm_step

(*| Unfold the definitions named in the list, and also every definition
    exposed by unfolding them.

    For example, `delta_only` unfolds `f1` to `f0 + 1`, while `delta_fully`
    also unfolds `f0`:

    ```fstar
    let f0 = 0
    let f1 = f0 + 1

    let _ = assert (norm [delta_only [`%f1]] f1 == f0 + 1)
    let _ = assert (norm [delta_fully [`%f1]] f1 == 0 + 1)
    ``` *)
val delta_fully (s: list string) : Tot norm_step

(*| Unfold the definitions marked with any of the given attributes.

    Tagging related definitions with a common attribute lets one step unfold
    them all:

    ```fstar
    irreducible let my_attr = ()

    [@@my_attr]
    let g0 = 0
    [@@my_attr]
    let g1 = g0 + 1

    let _ = assert (norm [delta_attr [`%my_attr]] g1 == 0 + 1)
    ``` *)
val delta_attr (s: list string) : Tot norm_step

(*| Unfold the definitions marked with any of the given qualifiers.

    For example, `delta_qualifier ["unfold"; "inline_for_extraction"]` unfolds
    definitions marked `unfold` or `inline_for_extraction`. *)
val delta_qualifier (s: list string) : Tot norm_step

(*| Unfold the definitions in any of the given namespaces.

    A namespace `A.B` covers the module `A.B` and its submodules, but not a
    module such as `A.BC`. *)
val delta_namespace (s: list string) : Tot norm_step

(*| Remove internal metadata nodes during normalization.

    Rarely needed explicitly. *)
val unmeta : norm_step

(*| Drop type and computation type ascriptions, such as `(e <: t)`, during
    normalization.

    This can make normalization faster, but ascriptions help when the result
    is typechecked again, and are sometimes necessary for it. Use with care. *)
val unascribe : norm_step

(*| Together with `FStar.NormSteps.iota`, reduce a projector applied to a
    constructor application, for example `Mktuple2?._1 (x, y)` to `x`. *)
val reduce_projections : norm_step
