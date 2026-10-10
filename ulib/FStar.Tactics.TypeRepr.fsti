module FStar.Tactics.TypeRepr

open FStar.Tactics.V2.Bare

private
let empty_elim (e:empty) (#a:Type) : a = match e with

(* Do not use directly. *)
(*| Computes the representation type of an inductive from its constructors: a nested `either` with one case per constructor, ending in `empty`, where each case is a nested `tuple2` of the constructor's arguments ending in `unit`.

    Internal to `FStar.Tactics.TypeRepr.entry`; do not use directly. *)
[@@plugin]
val generate_repr_typ (params : binders) (ctors : list ctor)  : Tac typ

(* Do not use directly. *)
(*| Solves a goal `t -> t_repr` by case analysis, mapping each constructor to the corresponding injection and tuple of the representation type.

    Internal to `FStar.Tactics.TypeRepr.entry`; do not use directly. *)
[@@plugin]
val generate_down () : Tac unit

(* Do not use directly. *)
(*| Solves a goal `t_repr -> t` for the inductive named `nm`, mapping each case of the representation back to its constructor.

    Internal to `FStar.Tactics.TypeRepr.entry`; do not use directly. Fails if
    `nm` is not an inductive type. *)
[@@plugin]
val generate_up (nm:string) () : Tac unit

(*| Generates, for the inductive type named `nm`, a representation type in terms of `either`, `tuple2`, `unit` and `empty`, and conversions between the two; use it as the body of a `%splice`.

    For a type `t` it generates `t_repr` (taking the same parameters as `t`),
    `t_down : t -> t_repr` and `t_up : t_repr -> t`, the latter two taking
    the parameters implicitly. Fails if `nm` is not found or is not an
    inductive type. For example:

    ```text
    %splice[test1_repr; test1_down; test1_up] (FStar.Tactics.TypeRepr.entry (`%test1))
    ```

    No proof that the conversions are inverses is generated; for some types
    `t_up (t_down x) == x` can be proved by SMT. *)
[@@plugin]
val entry (nm : string) : Tac decls
