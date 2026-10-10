module FStar.Stubs.Tactics.Types.Reflection

open FStar.Stubs.Reflection.Types
include FStar.Stubs.TypeChecker.Core
open FStar.Reflection.TermSpec

(* The compiler typing/subtyping/equivalence judgment tokens are indexed
   over the erasable model type [term_spec], so that the DSL typing
   judgment ([FStar.Reflection.Typing]) can bridge to them without any
   [denote_term] coercion at the token boundary. Their runtime
   representation on the compiler side is [unit], and [term_spec] is
   erasable, so this indexing is extraction-safe. *)
(*| A computation type for the typing tokens: an effect (total or ghost) paired with a result type in the model `FStar.Reflection.TermSpec.term_spec`.

    Used as the index of `FStar.Stubs.Tactics.Types.Reflection.typing_token`. *)
let comp_spec_typ = tot_or_ghost & term_spec

(* Typing reflection *)
(*| The compiler's judgment that a type is non-informative in an environment, that is, its values carry no computational content.

    An abstract proposition, implemented by the compiler; obtained from `FStar.Stubs.Tactics.V2.Builtins.is_non_informative`. *)
val non_informative_token (g:env) (t:term_spec) : prop
(*| The compiler's judgment that `t0` is a subtype of `t1` in an environment.

    An abstract proposition, implemented by the compiler; obtained from `FStar.Stubs.Tactics.V2.Builtins.check_subtyping`. *)
val subtyping_token (g:env) (t0 t1:term_spec) : prop
(*| The compiler's judgment that `t0` and `t1` are equivalent (definitionally equal) in an environment.

    An abstract proposition, implemented by the compiler; obtained for instance from `FStar.Stubs.Tactics.V2.Builtins.t_check_equiv`, `FStar.Stubs.Tactics.V2.Builtins.maybe_unfold_head` or `FStar.Stubs.Tactics.V2.Builtins.norm_well_typed_term`. *)
val equiv_token (g:env) (t0 t1:term_spec) : prop
(*| The compiler's typing judgment that `e` has the given effect and type in an environment.

    An abstract proposition, implemented by the compiler; obtained for instance from `FStar.Stubs.Tactics.V2.Builtins.core_check_term`, `FStar.Stubs.Tactics.V2.Builtins.core_compute_term_type` or `FStar.Stubs.Tactics.V2.Builtins.tc_term`. *)
val typing_token (g:env) (e:term_spec) (c:comp_spec_typ) : prop
