# Consumers of the ulib documentation

What the website and the MCP server need from the documentation of ulib,
and how the current prototypes measure up. Each acceptance case below was
run on the four pilot modules (`FStar.Option`, `FStar.List.Tot.Base`,
`FStar.Seq.Base`, `FStar.Classical`); the prototypes in this directory are
temporary, so the cases, not the prototypes, are the contract for their
replacements.

## Inputs

Both consumers read only the versioned JSON of `fstar.exe --export_docs`
(`fstar-module-docs`, version 4), produced from checked files whose sources
match. A `doc` is a list of lines written in the Markdown profile of
[AUTHORING.md](AUTHORING.md); `null` means undocumented. The portable
fixtures in [fixtures/](fixtures/) give doc payloads with the block
structure each one should parse to.

## MCP acceptance cases

Build an index with
`fstardoc_mcp.py index --fstar FSTAR --cache CACHE --include ulib --out IDX --module M ...`.
Results are asserted by inclusion, not by rank or by the exact result set.
A match by type is not evidence that a declaration applies.

| Case | Query | Expected | Prototype |
|---|---|---|---|
| Lookup | `lookup FStar.Seq.Base.slice` | its signature, contract, `documented: true` and the doc text | passes |
| Operator lookup | `lookup FStar.List.Tot.Base.op_At` | the record of `( @ )` | passes |
| Ambiguous name | `lookup index` | an error naming both `FStar.List.Tot.Base.index` and `FStar.Seq.Base.index` | passes |
| Type search | `find_by_type "seq a -> nat -> a"` | includes `FStar.Seq.Base.index` | passes |
| Type search | `find_by_type "list a -> nat -> a"` | includes `FStar.List.Tot.Base.index` | passes |
| Contract search | `find_by_contract FStar.Seq.Base.slice` | includes `lemma_len_slice` and `lemma_index_slice` | passes |
| Undocumented | `lookup` of a declaration with `doc: null` | says so, and does not present a description | passes (`lookup` adds a `note`) |

Gaps:

- Type search ranks lemmas such as `FStar.Classical.move_requires_2` above
  `FStar.Seq.Base.index` for `seq a -> nat -> a`, because a type variable
  matches any argument. Ranking is outside the documentation's control.
- The index flattens a doc to one string. A client that renders it must
  keep the line breaks; one that searches it should not search inside
  `fstar` fences as prose.
- Unsupported forms (effects, mutually recursive definitions; see
  `unsupported` in `ulib-docs-status.json`) are absent from the index, so
  "no result" does not mean that a name does not exist.

## Website acceptance cases

| Case | Expected | Prototype |
|---|---|---|
| Paragraphs, flat lists | one block per paragraph or item | `fstardoc_site.py` passes |
| Code spans | `<code>`, with the text unchanged | passes |
| Fully qualified names in code spans | link to the declaration when it is on the site | passes within a page (`#lemma_len_slice`) |
| `fstar` fences | a code block marked as F* | passes |
| Inline links | `<a href>` to the target | passes |
| Operators | a stable anchor, such as `op_At` for `( @ )` | passes |
| Base path | links work when the site is served under a path prefix | not tested; anchors are relative |
| `*strong*`, `_emphasis_` | strong and emphasis as the grammar defines them | fails in principle: the site uses CommonMark, where `*x*` is emphasis; the pilot avoids both |

`docs_json_to_html.py` shows a doc as verbatim text by design; it is the
reference rendering of the JSON, not of the Markdown.

## For the verified parser

- Parse each line list as the grammar's document; the fixtures' `.blocks`
  files give the expected block structure, and `fixtures/invalid` the
  payloads to reject. `fixtures/questions` lists inputs whose meaning the
  grammar should settle.
- Treat a fully qualified name in a code span as a candidate reference;
  resolving it is the renderer's job, against the declarations exported.
- Module and section prose is not exported yet. Until it is, a site cannot
  show module introductions from the JSON alone.
