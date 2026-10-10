(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Pprint

(* Unfortunate *)
open FStar.Char
open FStar.Float64

(* The rest of this file is taken almost verbatim from src/prettyprint/FStar.Pprint.fsti *)

(** A pretty-printing engine and a set of basic document combinators. *)

(** {1 Building documents} *)

(** Documents must be built in memory before they are rendered. This may seem
    costly, but it is a simple approach, and works well. *)

(** The following operations form a set of basic (low-level) combinators for
    building documents. On top of these combinators, higher-level combinators
    can be defined: see {!PPrintCombinators}. *)

(*| The abstract type of pretty-printer documents.

    A document describes text together with layout choices (where lines may
    break, how much to indent); `FStar.Pprint.render` or
    `FStar.Pprint.pretty_string` turns it into a string. Documents are built in
    memory before they are rendered.

    `FStar.Pprint` is an interface to François Pottier's OCaml PPrint library.
    Every operation in it is an assumed `val` with no F\* definition and no
    lemmas: the layout behaviour described in these docs is that of the
    library, not something F\* specifies or can prove. Documents cannot be
    inspected or compared in F\*. *)
new
val document : Type0

(** The following basic (low-level) combinators allow constructing documents. *)

(*| The empty document, which renders as nothing. *)
val empty: document

(*| A document consisting of a single character, which must not be a newline.

    Assumed primitive. Note that the OCaml implementation in the F\* library
    builds it with `PPrint.OCaml.char`, which prints the character as an OCaml
    character literal, quotes included. Use `FStar.Pprint.doc_of_string` for
    plain text. *)
val doc_of_char: char -> document

(*| A document consisting of the string `s`, which must not contain a newline.

    The newline restriction is not checked by the type; use
    `FStar.Pprint.arbitrary_string` for text that may contain newlines. See
    also `FStar.Pprint.utf8string` for strings whose display width differs
    from their byte length.

    ```fstar
    let call_doc (f: string) (args: list string) : FStar.Pprint.document =
      let open FStar.Pprint in
      group (doc_of_string f ^^ parens (separate_map (comma ^^ break_ 1) doc_of_string args))
    ``` *)
val doc_of_string: string -> document

(*| A document consisting of the boolean `b`, written `true` or `false`. *)
val doc_of_bool: bool -> document

(*| A document consisting of the portion of `s` that starts at offset `ofs` and has length `len`.

    The portion must not contain a newline, and the offset and length must
    designate a valid portion of `s`; neither condition is checked by the type. *)
val substring: string -> int -> int -> document

(*| A document consisting of the string `s`, whose apparent length is given explicitly.

    The string must not contain a newline. It may contain fancy characters
    (color escape sequences, UTF-8 or other multi-byte characters), so the
    number of columns it occupies on screen, `apparent_length`, may differ from
    its length in bytes; the layout engine uses the apparent length. *)
val fancystring: string -> int -> document

(*| A document consisting of a portion of `s`, given by offset and length, with an explicit apparent length.

    The combination of `FStar.Pprint.substring` and
    `FStar.Pprint.fancystring`: the portion must not contain a newline, and the
    last argument is the number of columns it occupies on screen. *)
val fancysubstring : string -> int -> int -> int -> document

(*| A document consisting of the UTF-8-encoded string `s`, which must not contain a newline.

    Unlike `FStar.Pprint.doc_of_string`, its width is measured in UTF-8 code
    points rather than bytes. *)
val utf8string: string -> document

(*| A forced newline.

    A `hardline` forces every enclosing `FStar.Pprint.group` to be printed in
    non-flattening mode, that is, it dissolves all enclosing groups. *)
val hardline: document

(*| A document consisting of `n` blank characters. *)
val blank: int -> document

(*| A potential line break: `n` blanks when printed flat, a newline otherwise.

    `break_` itself makes no choice: whether it is printed flat is decided by
    the enclosing `FStar.Pprint.group`. Called `break` in the OCaml library. *)
val break_: int -> document

(*| Concatenation of two documents, with no space or break in between. *)
val ( ^^ ) : document -> document -> document
(*| Concatenation of two documents separated by a breakable space.

    `x ^/^ y` is short for `x ^^ break_ 1 ^^ y`: a space when printed flat, a
    newline otherwise. *)
val ( ^/^ ) : document -> document -> document

(*| Increases the indentation level of a document by `j`.

    Indentation is inserted after every newline character in the document: `j`
    blanks are added after each newline. No indentation is inserted at the
    beginning of the document. See also `FStar.Pprint.align` and
    `FStar.Pprint.hang`. *)
val nest: int -> document -> document

(*| Introduces a layout choice: print the whole document on one line if possible.

    If the entire document fits on the current line, it is printed flat (every
    `FStar.Pprint.break_` becomes blanks). Otherwise the group is dissolved and
    the document is printed as is, where nested groups lead to further
    choices. A `FStar.Pprint.hardline` inside makes flattening impossible. *)
val group: document -> document

// (** [column f] is the document obtained by applying the function [f] to the
//     current column number. This combinator allows making the construction of
//     a document dependent on the current column number. *)
// val column: (int -> document) -> document

// (** [nesting f] is the document obtained by applying the function [f] to the
//     current indentation level, that is, the number of indentation (blank)
//     characters that were inserted at the beginning of the current line. *)
// val nesting: (int -> document) -> document

// (** [position f] is the document obtained by applying the function [f]
//     to the current position in the rendered output. The position
//     consists of [bol], which is the character-offset of the beginnig
//     of the current line (starting at 0), [line], which is the current
//     line (starting at 1), and [column], which is the current column
//     (starting at 0). The current character-offset is always given by
//     [bol + column]. *)
// val position : (int -> int -> int -> document) -> document

(*| Renders as `doc1` inside a group that is printed flat, and as `doc2` otherwise.

    Use with caution: because the printer is free to choose either document,
    the two should be semantically equivalent. *)
val ifflat: document -> document -> document

// SI: purposely commented-out for now.
// (** {1 Rendering documents} *)
//
// (** This renderer sends its output into an output channel. *)
// module ToChannel : PPrintRenderer.RENDERER
//   with type channel = out_channel
//    and type document = document
//
// (** This renderer sends its output into a memory buffer. *)
// module ToBuffer : PPrintRenderer.RENDERER
//   with type channel = Buffer.t
//    and type document = document
//
// (** This renderer sends its output into a formatter channel. *)
// module ToFormatter : PPrintRenderer.RENDERER
//   with type channel = Format.formatter
//    and type document = document


(** A set of high-level combinators for building documents. *)

(** {1 Single characters} *)

(** The following constant documents consist of a single character. *)

(*| A document consisting of a left parenthesis `(`. *)
val lparen: document
(*| A document consisting of a right parenthesis `)`. *)
val rparen: document
(*| A document consisting of a left angle bracket `<`. *)
val langle: document
(*| A document consisting of a right angle bracket `>`. *)
val rangle: document
(*| A document consisting of a left brace `{`. *)
val lbrace: document
(*| A document consisting of a right brace `}`. *)
val rbrace: document
(*| A document consisting of a left square bracket `[`. *)
val lbracket: document
(*| A document consisting of a right square bracket `]`. *)
val rbracket: document
(*| A document consisting of a single quote `'`. *)
val squote: document
(*| A document consisting of a double quote `"`. *)
val dquote: document
(*| A document consisting of a backquote (grave accent). *)
val bquote: document
(*| A document consisting of a semicolon `;`. *)
val semi: document
(*| A document consisting of a colon `:`. *)
val colon: document
(*| A document consisting of a comma `,`. *)
val comma: document
(*| A document consisting of a single space. *)
val space: document
(*| A document consisting of a dot `.`. *)
val dot: document
(*| A document consisting of a hash sign `#`. *)
val sharp: document
(*| A document consisting of a slash `/`. *)
val slash: document
(*| A document consisting of a single backslash character. *)
val backslash: document
(*| A document consisting of an equals sign `=`. *)
val equals: document
(*| A document consisting of a question mark `?`. *)
val qmark: document
(*| A document consisting of a tilde `~`. *)
val tilde: document
(*| A document consisting of an at sign `@`. *)
val at: document
(*| A document consisting of a percent sign `%`. *)
val percent: document
(*| A document consisting of a dollar sign `$`. *)
val dollar: document
(*| A document consisting of a caret `^`. *)
val caret: document
(*| A document consisting of an ampersand `&`. *)
val ampersand: document
(*| A document consisting of an asterisk `*`. *)
val star: document
(*| A document consisting of a plus sign `+`. *)
val plus: document
(*| A document consisting of a minus sign `-`. *)
val minus: document
(*| A document consisting of an underscore `_`. *)
val underscore: document
(*| A document consisting of an exclamation mark `!`. *)
val bang: document
(*| A document consisting of a vertical bar `|`. *)
val bar: document
(*| A document consisting of the arrow `->`. *)
val rarrow: document
(*| A document consisting of the long left arrow `<--`. *)
val long_left_arrow: document
(*| A document consisting of the left arrow `<-`. *)
val larrow: document

(** {1 Delimiters} *)

(*| Places a document `l` before `x`: `precede l x` is `l ^^ x`. *)
val precede: document -> document -> document

(*| Places a document `r` after `x`: `terminate r x` is `x ^^ r`. *)
val terminate: document -> document -> document

(*| Encloses a document between two delimiters: `enclose l r x` is `l ^^ x ^^ r`.

    No whitespace or line break is introduced. `FStar.Pprint.parens`,
    `FStar.Pprint.brackets` and similar are specializations. *)
val enclose: document -> document -> document -> document

(** The following combinators enclose a document within a pair of delimiters.
    They are partial applications of [enclose]. No whitespace or line break is
    introduced. *)

(*| Encloses a document in single quotes, with no whitespace or line break added. *)
val squotes: document -> document
(*| Encloses a document in double quotes, with no whitespace or line break added. *)
val dquotes: document -> document
(*| Encloses a document in backquotes, with no whitespace or line break added. *)
val bquotes: document -> document
(*| Encloses a document in braces `{` and `}`, with no whitespace or line break added. *)
val braces: document -> document
(*| Encloses a document in parentheses, with no whitespace or line break added. *)
val parens: document -> document
(*| Encloses a document in angle brackets `<` and `>`, with no whitespace or line break added. *)
val angles: document -> document
(*| Encloses a document in square brackets `[` and `]`, with no whitespace or line break added. *)
val brackets: document -> document

(** {1 Repetition} *)

(*| Concatenates two copies of a document. *)
val twice: document -> document

(*| Concatenates `n` copies of a document. *)
val repeat: int -> document -> document

(** {1 Lists and options} *)

(*| Concatenates a list of documents with `FStar.Pprint.op_Hat_Hat`, adding no separator. *)
val concat: list document -> document

(*| Concatenates a list of documents, inserting `sep` between every two adjacent documents.

    See also `FStar.Pprint.separate_map`, `FStar.Pprint.separate2` and
    `FStar.Pprint.flow`. *)
val separate: document -> list document -> document

(*| Maps each element of a list to a document and concatenates the results.

    `concat_map f xs` is equivalent to `concat (List.map f xs)`. *)
val concat_map: ('a -> document) -> list 'a -> document

(*| Maps each element of a list to a document and concatenates the results with a separator.

    `separate_map sep f xs` is equivalent to `separate sep (List.map f xs)`. *)
val separate_map: document -> ('a -> document) -> list 'a -> document

(*| Concatenates a list of documents with a separator, using a different separator before the last one.

    `sep` is inserted between every two adjacent documents except the last two,
    which are separated by `last_sep` (as in "a, b and c"). *)
val separate2: document -> document -> list document -> document

(*| Renders an optional value: the empty document for `None`, and `f x` for `Some x`. *)
val optional: ('a -> document) -> option 'a -> document

(** {1 Text} *)

(*| Splits a string at newline characters and turns each line into a document.

    Each line becomes a `FStar.Pprint.substring`; the newlines are dropped.
    This is not UTF-8 aware. *)
val lines: string -> list document

(*| A document for a string that may contain newlines.

    Equivalent to `separate (break_ 1) (lines s)`: each newline of `s` becomes
    a potential line break, printed as a space when the enclosing group is
    flat. Use it instead of `FStar.Pprint.doc_of_string` when `s` may contain
    newlines. *)
val arbitrary_string: string -> document

(*| Splits a string at whitespace and turns each word into a document.

    All whitespace is discarded. This is not UTF-8 aware. Often combined with
    `FStar.Pprint.flow` to typeset a paragraph. *)
val words: string -> list document

(*| Splits a string before and after every character satisfying `ok`, giving a list of documents.

    Each matching character becomes a document of its own. No information is
    lost: concatenating the documents yields the original string. This is not
    UTF-8 aware. *)
val split: (char -> bool) -> string -> list document

(*| Separates a list of documents with `sep` and starts a new line whenever the next document does not fit.

    Useful for free-flowing, ragged-right text. A typical separator is
    `break_ b`, where `b` is the number of spaces between two consecutive words
    on the same line. See also `FStar.Pprint.words`. *)
val flow: document -> list document -> document

(*| Maps each element of a list to a document and lays out the results with `FStar.Pprint.flow`.

    `flow_map sep f xs` is equivalent to `flow sep (List.map f xs)`. *)
val flow_map: document -> ('a -> document) -> list 'a -> document

(*| A possible way of displaying a URL.

    A potential line break is inserted immediately before and immediately after
    every slash and dot character. *)
val url: string -> document

(** {1 Alignment and indentation} *)

(*| Sets the indentation level of a document to the current column.

    The document is thus rendered within a box whose upper left corner is the
    current position. See also `FStar.Pprint.hang` and `FStar.Pprint.nest`. *)
val align: document -> document

(*| Like `FStar.Pprint.align`, but additionally indents every line except the first by `n`.

    The text in the box forms a hanging indent. *)
val hang: int -> document -> document

(*| Lays out `left` and `right` on one line if they fit, otherwise puts `right` on the next line, indented.

    Flat layout: `left right`, with `b` spaces between them. Non-flat layout:
    `left`, then a newline, then `right` nested by `n`. The choice is made by a
    `FStar.Pprint.group` around the whole. *)
val prefix: int -> int -> document -> document -> document

(*| Lays out `right` after a potential line break: `jump n b right` is `prefix n b empty right`.

    Flat, `right` is preceded by `b` spaces; otherwise it starts on a new line
    nested by `n`. *)
val jump: int -> int -> document -> document

(*| Lays out a binary operator application `left middle right` on one line, or breaks after `middle`.

    Flat layout: `left middle right`. Non-flat layout: `left middle` on one
    line and `right` on the next, nested by `n`. `b` is the number of spaces
    between `left` and `middle` (always) and between `middle` and `right`
    (when flat). *)
val infix: int -> int -> document -> document -> document -> document

(*| Lays out `opening contents closing` on one line if they fit, otherwise on three lines with `contents` indented.

    Flat layout: `opening contents closing`, with `b` spaces on each side of
    `contents`. Non-flat layout: `opening`, `contents` and `closing` on
    separate lines, `contents` nested by `n`. See also
    `FStar.Pprint.soft_surround`. *)
val surround: int -> int -> document -> document -> document -> document

(*| Like `FStar.Pprint.surround`, but with intermediate layouts between fully flat and fully broken.

    It uses more than one group: it tries to keep the beginning of `contents`
    on the same line as `opening`, and `closing` on the same line as the end
    of `contents`, when possible. *)
val soft_surround: int -> int -> document -> document -> document -> document

(*| Surrounds a separated list with delimiters, or produces `void` when the list is empty.

    `surround_separate n b void opening sep closing docs` is
    `surround n b opening (separate sep docs) closing` when `docs` is
    nonempty, and `void` otherwise.

    ```fstar
    let block_doc (body: list FStar.Pprint.document) : FStar.Pprint.document =
      let open FStar.Pprint in
      surround_separate 2 1 (lbrace ^^ rbrace) lbrace (semi ^^ break_ 1) rbrace body
    ``` *)
val surround_separate: int -> int -> document -> document -> document -> document -> list document -> document

(*| Like `FStar.Pprint.surround_separate`, applied to the documents obtained by mapping `f` over a list.

    Equivalent to `surround_separate n b void opening sep closing (List.map f xs)`. *)
val surround_separate_map: int -> int -> document -> document -> document -> document -> ('a -> document) -> list 'a -> document

(** {1 Short-hands} *)


//(** [!^s] is a short-hand for [string s]. *)
// val ( !^ ) : string -> document

(** [x ^/^ y] separates [x] and [y] with a breakable space.
    It is a short-hand for [x ^^ break 1 ^^ y]. *)

(** [x ^//^ y] is a short-hand for [prefix 2 1 x y]. *)
// val ( ^//^ ) : document -> document -> document

// Expose underlying Renderer.pretty implementations (avoid inner modules).
// [pretty_string] uses ToBuffer:RENDERER implementation;
// [print_out_channel] uses the ToChannel:RENDERER one.
(*| Renders a document to a string, given a ribbon fraction and a maximum line width.

    The first argument is the ribbon fraction (the maximal fraction of the
    line width occupied by non-indentation text) and the second the line width
    in columns. A `float64` can be built with `FStar.Float64` (for example
    `FStar.Float64.one`). `FStar.Pprint.render` uses default settings. *)
val pretty_string : float64 -> int -> document -> string

(*| Renders a document to a string with default settings.

    Equivalent to `pretty_string 1.0 80`: a ribbon fraction of 1.0 and a line
    width of 80 columns. Assumed primitive, implemented in OCaml. *)
val render : document -> string
