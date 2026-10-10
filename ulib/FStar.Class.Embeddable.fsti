module FStar.Class.Embeddable

open FStar.Reflection.V2

(*| Typeclass of types whose values can be turned into syntax terms (`FStar.Stubs.Reflection.Types.term`) in tactics and metaprograms.

    Fields:

    - `embed`: builds a term denoting the given value.
    - `typ`: the term for the type `a` itself.

    Instances exist for `string`, `bool`, `int` and lists of embeddable types. *)
class embeddable (a:Type) = {
  embed : a -> Tot term;
  typ : term;
}

(*| Embeds a string as a string constant term. *)
instance val embeddable_string : embeddable string
(*| Embeds a boolean as the constant `true` or `false`. *)
instance val embeddable_bool   : embeddable bool
(*| Embeds an integer as a decimal integer constant term. *)
instance val embeddable_int    : embeddable int

(*| Embeds a list as a term built from `Nil` and `Cons`, applied to the element type and the embedded elements. *)
instance val embeddable_list (a:Type) (ea : embeddable a) : embeddable (list a)
