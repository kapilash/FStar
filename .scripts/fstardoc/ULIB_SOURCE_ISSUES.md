# ulib source issues found while documenting

While writing structured documentation for `ulib`, we found the issues below
in existing code, contracts and comments. The documentation describes the
actual behaviour and warns about each problem where relevant. Apart from the
proof fragility in the last section, none of the code has been changed; each
fix needs a separate decision. Line numbers are approximate.

## Soundness

- `ulib/FStar.Bytes.fsti` (`repr_bytes_size`, around line 271): the assumed
  interface is inconsistent. `repr_bytes` returns a `pos`, but
  `repr_bytes_size 0 0` concludes `repr_bytes 0 <= 0`.
  `let bad () : Lemma False = FStar.Bytes.repr_bytes_size 0 0` verifies.
  `FStar.Bytes` has no `.fst`; it is realized in OCaml.

## Behaviour that contradicts names or old comments

- `ulib/FStar.Int.fsti` (`incr_mod`, `decr_mod`, around line 124): these compute
  `(a + 1) % pow2 (n - 1)` and `(a - 1) % pow2 (n - 1)`. The result is always
  non-negative, which is not two's-complement wrap-around. `add_mod` and
  `sub_mod` behave as expected.
- `ulib/FStar.RBMap.fst` (`for_any`, around line 144): checks the root and then
  applies `for_all` to the subtrees, so it can return `false` even when some
  binding satisfies the predicate.
- `ulib/FStar.Error.fst` (`unexpected`, `unreachable`): the old comment called
  them aliases for `failwith`. They actually print a message and loop forever;
  they never raise.
- `ulib/FStar.Fin.fsti` (`is_symmetric_intro` around line 149,
  `is_transitive_intro` around line 158): both conclude reflexivity instead of
  symmetry or transitivity.
- `ulib/FStar.Char.fsti` (`char_code`, line 46): the refinement is
  `v n < 0xd7ff`, which excludes the valid scalar value `0xd7ff`. The surrogate
  range starts at `0xd800`.
- `ulib/FStar.Algebra.CommMonoid.Fold.fsti` (`init_func_from_expr`, around
  line 45): index `i` maps to `expr (n0 + i)` instead of `expr (a + i)`. This
  is correct only when `a = n0`.
- `ulib/FStar.List.fst` (`sortWith`, ML): sorts in descending order with respect
  to the comparison, unlike `FStar.List.Tot.Base.sortWith`.
- `ulib/FStar.Reflection.Const.fst` (`eq1_qn`): names `Prims.eq`, which does
  not exist; boolean equality is `Prims.op_Equals`. As a result
  `FStar.Reflection.V2.Formula.term_as_formula` never produces `Comp BoolEq`
  for `x = y`, and `formula_to_term` builds an ill-typed term for it.
- `ulib/FStar.Reflection.V2.Arith.fst` (`expr_to_string`): `Ladd`, `Lsub` and
  `Shr` all print as `>>`.
- `ulib/FStar.Reflection.V2.Compare.fst` (`compare_term`): any two `Tv_Match`
  terms compare `Eq` (marked `TODO`).
- `ulib/FStar.Reflection.V2.Formula.fst` (`formula_as_term_view`): `Forall`
  and `Exists` map to `Tv_Unknown` (marked `TODO`).
- `ulib/FStar.Tactics.CanonCommMonoid.fst` (`const_last`, `special_first`): the
  old comments had the orderings reversed (constants go first; special terms
  go last). The non-special terms all compare equal under an unstable sort,
  so the two sides of an equation may be ordered differently and `trefl` can
  fail.
- `ulib/FStar.Tactics.CanonMonoid.fst` (`canon_monoid`): sends the original
  goal to SMT as well, and cannot handle `FStar.List.Tot.Base.append`.
- `ulib/FStar.Tactics.CanonCommMonoidSimple.Equiv.fst` (`reification`): ignores
  its `eq` argument.
- `ulib/FStar.Tactics.PatternMatching.fst` (`pm`): the old comment called it
  greedy; it backtracks over hypotheses.
- `ulib/FStar.Tactics.PrettifyType.fsti` (`entry`): the old comment promised a
  generated `_bij` bijection, but that generation is commented out.
- `ulib/FStar.Stubs.Tactics.V2.Builtins.fsti`: old comments named
  nonexistent normalization steps (`simpl`, `whnf`) and a nonexistent
  `set_dump_failure`; `intro_rec` is marked broken (issue 1103).
- `ulib/FStar.Tactics.CanonCommSemiring.fst` (`canon_semiring`): binary `-` on
  `int` is treated as an opaque variable; write `x + - y`.

## Gaps between specification and implementation

- `ulib/FStar.Bytes.fsti`:
  - `string_of_hex`, `bytes_of_hex` and parts of `bytes_of_int` are typed
    `Tot`, but the OCaml realization calls `failwith` on bad input.
  - Several functions specify only the length of their result: `abyte`,
    `twobytes`, `xor` and `utf8_encode`.
  - `split_` requires `k < length b`, unlike `split`.
- `ulib/FStar.BV.fsti` (`bvdiv_unsafe`, `bvmod_unsafe`): the hidden
  implementation returns 0 for a zero divisor. SMT-LIB `bvudiv` and `bvurem`
  define different results, so the model and the solver may disagree.
- `ulib/FStar.Endianness.fsti` (`le_of_seq_uint64`): no lemma specifies its
  contents.

## Stale module or section prose

- `ulib/FStar.Real.Dedekind.fsti` (line 21): says `FStar.Real` is entirely
  axiomatized. It is now implemented on top of `FStar.Real.Dedekind`; only its
  SMT mapping is assumed.
- `ulib/FStar.Sequence.Base.fsti` (around line 645): mentions
  `all_dafny_seq_facts_lemma` (the real name is `all_seq_facts_lemma`) and an
  alias `nil` that does not exist.
- `ulib/FStar.All.fsti` (line 39): "References support decidable equality",
  but `ref` is declared in `Type0`, not `eqtype`.
- `ulib/FStar.Algebra.CommMonoid.Equiv.fst` (`right_identity`): a note says
  the universe is fixed to `u#1`, but the code uses `u#aa`.
- `ulib/FStar.Reflection.TermSpec.fst`: a section comment cites
  `FStar.Reflection.Typing.subst_term` and `denote_subst_term`, which do not
  exist.

## Proof fragility (fixed)

- `ulib/FStar.Matrix.fst` (`matrix_mul_is_left_distributive`,
  `matrix_mul_is_right_distributive`): the unmodified proofs fail for some Z3
  seeds, and adding documentation to `FStar.Matrix.fsti` triggered the failure.
  A private helper, `matrix_mul_ijth_eq_sum_of_pointwise_init`, stabilizes
  both proofs; they verified with seeds 0 to 5. The lemma statements are
  unchanged.
