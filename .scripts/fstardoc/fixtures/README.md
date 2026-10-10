# Shared documentation fixtures

Each `.md` file is the payload of one doc comment, exactly as the export
reports it after the compiler has dedented it. These files are meant to be
read by every consumer of the documentation: the conservative lint today,
and the verified Markdown parser, the HTML generator and the MCP server
later. They are tied to `../../../MinimalMarkdownGrammar.md` and to the
profile in `../AUTHORING.md`.

- `valid/` holds text that follows the authoring profile. Each `X.md` has
  an `X.blocks` file giving the structure a parser is expected to produce,
  as an indented tree: `paragraph`, `heading N`, `list`/`item`,
  `code_block "info"` with `line`s, and inline `text`, `code`, `strong`,
  `emph`, `link "target"` and `softbreak`. Escapes are resolved in `text`.
- `invalid/` holds text the profile rejects. `make fixtures` checks that
  the lint rejects each file and accepts every file in `valid/`.
- `questions/` holds text whose meaning the grammar does not yet settle.
  The profile steers authors away from all of it. These are inputs for the
  parser effort, not a decision about their meaning:
  - `delimiter-run.md`: a run of `*` that is both an opener and literal text.
  - `intraword-delimiters.md`: `*` and `_` between word characters, where
    a run is both an opener and a closer candidate.
  - `mismatched-fence.md`: `FenceClose` accepts either marker, so a block
    opened with backticks can be closed with tildes.
  - `inline-in-heading.md`: whether heading text is parsed as inline content.
  - `inline-in-link-label.md`: `LinkText` is plain characters, so a code
    span inside a label is literal.
  - `no-final-newline.md`: every block in the grammar ends with a newline,
    but the export's last line has none.

The `.blocks` files describe intent. Until the verified parser runs them,
nothing checks them.
