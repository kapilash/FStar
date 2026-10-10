#!/usr/bin/env python3
"""Inventory, coverage and conservative checks for ulib documentation.

Inputs are the tracked top-level ulib sources, the versioned JSON that
`fstar.exe --export_docs` writes (schema "fstar-module-docs", version 4),
and the status file `ulib-docs-status.json` beside this script. The script
never opens a checked file itself.

    ulib_docs.py manifest
    ulib_docs.py export   --fstar EXE --cache DIR --out DIR [--module M ...]
    ulib_docs.py audit    [--module M ...]
    ulib_docs.py coverage --exports DIR [--module M ...] [--check] [--json FILE]
    ulib_docs.py lint     --exports DIR [--module M ...]
    ulib_docs.py check    --exports DIR

`check` is the gate: every module listed as completed in the status file
must export, have every eligible declaration documented (or explicitly
excluded), pass `lint`, and have its `fstar` examples present in a checked
example file. Modules that are not completed are reported, not failed.

Like the other generators here, this script is temporary. The lint is a
conservative check of the authoring profile in AUTHORING.md, written
without a Markdown parser; it is not a conformance check against the
grammar, which awaits the verified parser.
"""

import argparse
import json
import os
import re
import subprocess
import sys

SCHEMA, VERSION = "fstar-module-docs", 4

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
STATUS = os.path.join(HERE, "ulib-docs-status.json")
EXAMPLES_DIR = os.path.join(ROOT, "tests", "docs", "ulib")

# Kinds whose documentation is attached to the declaration itself.
# Constructors cannot carry their own documentation in the current export:
# they are described by their parent type's documentation.
ELIGIBLE_KINDS = ("val", "let", "type", "assume")
PARENT_KINDS = ("constructor",)

GENERATED_MARK = "THIS MODULE IS GENERATED AUTOMATICALLY"


# ---------------------------------------------------------------- manifest

def tracked_sources():
    r = subprocess.run(["git", "ls-files", "ulib/*.fst", "ulib/*.fsti"],
                       cwd=ROOT, capture_output=True, text=True, check=True)
    return [p for p in r.stdout.split() if p.count("/") == 1]


def manifest():
    """One entry per top-level module, in name order. The authoritative
    source is the interface when there is one: it is what the export
    documents."""
    mods = {}
    for p in tracked_sources():
        base = os.path.basename(p)
        name, ext = os.path.splitext(base)
        mods.setdefault(name, {})[ext] = p
    out = []
    for name in sorted(mods):
        srcs = mods[name]
        auth = srcs.get(".fsti") or srcs[".fst"]
        with open(os.path.join(ROOT, auth), encoding="utf-8") as f:
            text = f.read()
        out.append({
            "module": name,
            "source": auth,
            "interface": auth.endswith(".fsti"),
            "generated": GENERATED_MARK in text,
        })
    return out


def select(entries, modules):
    if not modules:
        return entries
    known = {e["module"]: e for e in entries}
    missing = [m for m in modules if m not in known]
    if missing:
        sys.exit("not top-level ulib modules: %s" % ", ".join(missing))
    return [known[m] for m in modules]


def load_status():
    with open(STATUS, encoding="utf-8") as f:
        st = json.load(f)
    st.setdefault("completed", [])
    st.setdefault("exclusions", {})
    st.setdefault("unsupported", {})
    st.setdefault("blocked", {})
    return st


# ------------------------------------------------------------------ export

def find_checked(module, cache):
    for ext in (".fsti.checked", ".fst.checked"):
        p = os.path.join(cache, module + ext)
        if os.path.exists(p):
            return p
    return None


def cmd_export(args):
    entries = select(manifest(), args.module)
    os.makedirs(args.out, exist_ok=True)
    failed = []
    for e in entries:
        m = e["module"]
        checked = find_checked(m, args.cache)
        if checked is None:
            failed.append((m, "no checked file in %s" % args.cache))
            continue
        cmd = [args.fstar, "--include", os.path.join(ROOT, "ulib"),
               "--export_docs", os.path.abspath(checked)]
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode != 0:
            failed.append((m, r.stderr.strip().splitlines()[-1:] or ["failed"]))
            continue
        data = json.loads(r.stdout)
        if data.get("schema") != SCHEMA or data.get("version") != VERSION:
            failed.append((m, "unexpected schema %s/%s"
                           % (data.get("schema"), data.get("version"))))
            continue
        with open(os.path.join(args.out, m + ".json"), "w", encoding="utf-8") as f:
            f.write(r.stdout)
        if r.stderr.strip():
            sys.stderr.write("%s:\n%s\n" % (m, r.stderr.rstrip()))
    print("exported %d of %d modules" % (len(entries) - len(failed), len(entries)))
    for m, why in failed:
        print("  FAILED %s: %s" % (m, why))
    return 1 if failed else 0


def load_export(exports, module):
    p = os.path.join(exports, module + ".json")
    if not os.path.exists(p):
        return None
    with open(p, encoding="utf-8") as f:
        return json.load(f)


# ------------------------------------------------------------------- audit

# Public declaration forms the export omits. This is a line-oriented
# scan of the authoritative source, not a parser: it reports candidates
# for the gap ledger, which a human then confirms in the status file.
AUDIT_RULES = [
    ("effect", re.compile(
        r"^\s*(?:(?:total|reifiable|reflectable|inline_for_extraction|unfold|assume|"
        r"noextract|irreducible)\s+)*"
        r"(new_effect|layered_effect|sub_effect|polymonadic_bind|polymonadic_subcomp|effect)\b")),
    ("splice", re.compile(r"^\s*%splice")),
    ("mutual-recursion", re.compile(r"^and\s+[^\s(]")),
]


def strip_comments(text):
    """Blank out F* comments, keeping line structure. Nested block
    comments and line comments are handled; strings are not, which is
    adequate for a candidate scan."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("(*", i) and not text.startswith("(*)", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif not depth and text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        else:
            c = text[i]
            out.append(c if (not depth or c == "\n") else " ")
            i += 1
    return "".join(out)


def audit_module(entry):
    with open(os.path.join(ROOT, entry["source"]), encoding="utf-8") as f:
        lines = strip_comments(f.read()).splitlines()
    found = []
    for n, line in enumerate(lines, 1):
        for kind, rx in AUDIT_RULES:
            if rx.search(line):
                prev = lines[n - 2] if n > 1 else ""
                if "private" in line.split() or prev.strip() == "private":
                    continue
                found.append({"kind": kind, "line": n, "text": line.strip()[:100]})
    return found


def cmd_audit(args):
    st = load_status()
    total = 0
    for e in select(manifest(), args.module):
        found = audit_module(e)
        if not found:
            continue
        total += len(found)
        print("%s (%s)" % (e["module"], e["source"]))
        for x in found:
            print("  %-16s line %-5d %s" % (x["kind"], x["line"], x["text"]))
        if e["module"] in st["unsupported"]:
            print("  ledger: %s" % st["unsupported"][e["module"]])
    print("%d candidate unsupported public forms" % total)
    return 0


# ---------------------------------------------------------------- coverage

def classify(module, data, st):
    eligible, documented, excluded, parent, missing = 0, 0, 0, 0, []
    for d in data["declarations"]:
        if d["kind"] in PARENT_KINDS:
            parent += 1
            continue
        if d["kind"] not in ELIGIBLE_KINDS:
            missing.append(d["name"] + " (unknown kind %s)" % d["kind"])
            continue
        eligible += 1
        if d.get("doc") is not None:
            documented += 1
        elif d["name"] in st["exclusions"]:
            excluded += 1
        else:
            missing.append(d["name"])
    return {"module": module, "eligible": eligible, "documented": documented,
            "excluded": excluded, "constructors": parent, "missing": missing}


def coverage(exports, entries, st):
    rows, absent = [], []
    for e in entries:
        data = load_export(exports, e["module"])
        if data is None:
            absent.append(e["module"])
            continue
        r = classify(e["module"], data, st)
        r["generated"] = e["generated"]
        r["completed"] = e["module"] in st["completed"]
        r["blocked"] = e["module"] in st["blocked"]
        rows.append(r)
    return rows, absent


def cmd_coverage(args):
    st = load_status()
    entries = select(manifest(), args.module)
    rows, absent = coverage(args.exports, entries, st)
    tot = {"eligible": 0, "documented": 0, "excluded": 0, "constructors": 0}
    for r in rows:
        for k in tot:
            tot[k] += r[k]
        mark = "*" if r["completed"] else "!" if r["blocked"] else " "
        print("%s %-48s %4d/%-4d documented  %3d excluded  %3d constructors%s"
              % (mark, r["module"], r["documented"], r["eligible"], r["excluded"],
                 r["constructors"], "  [generated]" if r["generated"] else ""))
        if args.verbose:
            for n in r["missing"]:
                print("      undocumented: %s" % n)
    done = sum(1 for r in rows if r["completed"])
    blocked = sum(1 for r in rows if r["blocked"])
    print("\n%d modules exported, %d not exported, %d completed (*), %d blocked (!)"
          % (len(rows), len(absent), done, blocked))
    print("%d/%d eligible declarations documented, %d excluded; "
          "%d constructors covered by their parent type"
          % (tot["documented"], tot["eligible"], tot["excluded"], tot["constructors"]))
    print("%d modules with candidate unsupported public forms (see `audit`)"
          % sum(1 for e in entries if audit_module(e)))
    if absent:
        print("not exported: %s" % ", ".join(absent))
    if args.json:
        with open(args.json, "w", encoding="utf-8") as f:
            json.dump({"modules": rows, "not_exported": absent, "totals": tot}, f, indent=1)
    return 0


# -------------------------------------------------------------------- lint

FENCE = re.compile(r"^\s*(```|~~~)(.*)$")
CODE_SPAN = re.compile(r"`[^`]+`")
EMPTY_CODE = re.compile(r"``")
ESCAPE = re.compile(r"\\[*_`\[\]()\\]")
LINK = re.compile(r"\[[^\]\n]*\]\([^)\n]*\)")
BULLET = re.compile(r"^\s*[-*+][ \t]")
HEADING = re.compile(r"^\s*(#+)(?:[ \t]|$)")
# A delimiter pair the grammar reads unambiguously: opened after start or
# whitespace, closed before end, whitespace or punctuation, and with no
# whitespace just inside either delimiter.
STRONG = re.compile(r"(?:(?<=^)|(?<=[\s(]))\*[^\s*][^*]*?(?<=[^\s*])\*(?=$|[\s.,;:!?)])|"
                    r"(?:(?<=^)|(?<=[\s(]))\*[^\s*]\*(?=$|[\s.,;:!?)])")
EMPH = re.compile(r"(?:(?<=^)|(?<=[\s(]))_[^\s_][^_]*?(?<=[^\s_])_(?=$|[\s.,;:!?)])|"
                  r"(?:(?<=^)|(?<=[\s(]))_[^\s_]_(?=$|[\s.,;:!?)])")

LINE_RULES = [
    (re.compile(r"^\s*\d+[.)][ \t]"), "ordered list; use a `- ` list or prose"),
    (re.compile(r"^\s*>"), "block quote"),
    (re.compile(r"^\s*\|.*\|\s*$"), "table"),
    (re.compile(r"^\s*(=+|-{2,})\s*$"), "setext underline or thematic break"),
]
INLINE_RULES = [
    (re.compile(r"<[A-Za-z/!]"), "raw HTML"),
    (re.compile(r"\{\[|\]\}"), "legacy {[ ... ]} code block; use a fenced block"),
    (re.compile(r"\[[^\]\n]*\](?!\()"), "bracket reference; use a code span or an inline link"),
]


def lint_doc(lines):
    """Problems with one doc payload, as (line index, message)."""
    probs = []
    fence = None
    prev_item = False
    for i, raw in enumerate(lines):
        m = FENCE.match(raw)
        if fence is not None:
            if m and m.group(1) == fence and not m.group(2).strip():
                fence = None
            continue
        if m:
            fence = m.group(1)
            prev_item = False
            continue
        if not raw.strip():
            prev_item = False
            continue
        if raw.rstrip() != raw:
            probs.append((i, "trailing whitespace"))
        for rx, msg in LINE_RULES:
            if rx.search(raw):
                probs.append((i, msg))
        is_item = bool(BULLET.match(raw))
        if prev_item and not is_item:
            probs.append((i, "a list item is one line; this continuation becomes a paragraph"))
        if is_item and re.match(r"^[ \t]{2,}", raw):
            probs.append((i, "nested or indented list item"))
        h = HEADING.match(raw)
        if h and len(h.group(1)) > 6:
            probs.append((i, "more than six # in a heading"))
        prev_item = is_item

        line = ESCAPE.sub("", raw)
        if EMPTY_CODE.search(line):
            probs.append((i, "empty code span or double backtick"))
        if re.search(r"\[[^\]\n]*`[^\]\n]*\]\(", line):
            probs.append((i, "code span in a link label; the label is plain text"))
        line = CODE_SPAN.sub("", line)
        if "`" in line:
            probs.append((i, "unbalanced backtick; a code span cannot cross a line"))
        line = LINK.sub("L", line)
        for rx, msg in INLINE_RULES:
            if rx.search(line):
                probs.append((i, msg))
        if is_item:
            line = BULLET.sub("", line, count=1)
        line = STRONG.sub("S", line)
        line = EMPH.sub("E", line)
        if "*" in line or "_" in line:
            probs.append((i, "bare * or _ outside a code span; put identifiers and "
                             "operators in code spans, or escape it"))
    if fence is not None:
        probs.append((len(lines) - 1, "unclosed code fence"))
    return probs


def fstar_examples(lines):
    """The bodies of the ```fstar fences in a doc payload."""
    out, cur = [], None
    for raw in lines:
        m = FENCE.match(raw)
        if cur is None:
            if m and m.group(2).strip() == "fstar":
                cur = []
        elif m and not m.group(2).strip():
            out.append("\n".join(cur))
            cur = None
        else:
            cur.append(raw)
    return out


def example_corpus():
    corpus = []
    if os.path.isdir(EXAMPLES_DIR):
        for fn in sorted(os.listdir(EXAMPLES_DIR)):
            if fn.endswith((".fst", ".fsti")):
                with open(os.path.join(EXAMPLES_DIR, fn), encoding="utf-8") as f:
                    corpus.append(normalize(f.read()))
    return corpus


def normalize(s):
    return "\n".join(l.rstrip() for l in s.strip().splitlines())


def lint_module(data, corpus):
    probs = []
    for d in data["declarations"]:
        doc = d.get("doc")
        if doc is None:
            continue
        for i, msg in lint_doc(doc):
            probs.append("%s, doc line %d: %s" % (d["name"], i + 1, msg))
        for ex in fstar_examples(doc):
            ex = normalize(ex)
            if not any(ex in c for c in corpus):
                probs.append("%s: ```fstar example not found verbatim in %s"
                             % (d["name"], os.path.relpath(EXAMPLES_DIR, ROOT)))
    return probs


def cmd_lint(args):
    corpus = example_corpus()
    bad = 0
    for e in select(manifest(), args.module):
        data = load_export(args.exports, e["module"])
        if data is None:
            continue
        for p in lint_module(data, corpus):
            print("%s: %s" % (e["module"], p))
            bad += 1
    print("%d problems" % bad)
    return 1 if bad else 0


def cmd_lint_file(args):
    """Lint raw doc payloads, one per file: the shared fixture format."""
    bad = 0
    for fn in args.files:
        with open(fn, encoding="utf-8") as f:
            lines = f.read().split("\n")
        if lines and lines[-1] == "":
            lines.pop()
        for i, msg in lint_doc(lines):
            print("%s:%d: %s" % (fn, i + 1, msg))
            bad += 1
    return 1 if bad else 0


def _doc_lines_of_text(body):
    """Mirror doc_lines_of_text in src/parser/FStarC.Parser.Lexer.fst."""
    def indent(s):
        t = len(s) - len(s.lstrip(" \t"))
        return -1 if t == len(s) else t
    lines = [l.rstrip(" \t\r") for l in body.split("\n")]
    k = indent(lines[0])
    lines[0] = "" if k < 0 else lines[0][k:]
    ind = [indent(l) for l in lines[1:] if indent(l) >= 0]
    common = min(ind) if ind else 0
    lines = lines[:1] + [l[common:] for l in lines[1:]]
    while lines and lines[0] == "":
        lines.pop(0)
    while lines and lines[-1] == "":
        lines.pop()
    return lines


def source_docs(text):
    """Yield (line, payload lines) for each (*| ... *) block in F* source.

    A lightweight scanner: it skips strings, line comments and ordinary
    (nested) comments; it is not an F* lexer."""
    i, n, line, depth = 0, len(text), 1, 0
    while i < n:
        c = text[i]
        if c == "\n":
            line += 1
            i += 1
        elif depth == 0 and text.startswith("(*|", i):
            start, j, d, buf = line, i + 3, 0, []
            while j < n:
                if text.startswith("(*", j):
                    d += 1
                    buf.append("(*")
                    j += 2
                elif text.startswith("*)", j):
                    if d == 0:
                        break
                    d -= 1
                    buf.append("*)")
                    j += 2
                else:
                    buf.append(text[j])
                    j += 1
            body = "".join(buf)
            line += body.count("\n")
            yield start, _doc_lines_of_text(body)
            i = j + 2
        elif text.startswith("(*", i) and not text.startswith("(*)", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
        elif depth == 0 and text.startswith("//", i):
            while i < n and text[i] != "\n":
                i += 1
        elif depth == 0 and c == '"':
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    i += 1
                elif text[i] == "\n":
                    line += 1
                i += 1
            i += 1
        else:
            i += 1


def cmd_lint_source(args):
    """Lint the (*| ... *) docs of F* sources before export."""
    corpus = example_corpus()
    bad = 0
    for fn in args.files:
        with open(fn, encoding="utf-8") as f:
            text = f.read()
        for start, lines in source_docs(text):
            probs = list(lint_doc(lines))
            if not lines:
                probs.append((0, "blank documentation"))
            for ex in fstar_examples(lines):
                if not any(normalize(ex) in c for c in corpus):
                    probs.append((0, "```fstar example not found verbatim in %s"
                                  % os.path.relpath(EXAMPLES_DIR, ROOT)))
            for i, msg in probs:
                print("%s:%d: %s" % (fn, start + i, msg))
                bad += 1
    return 1 if bad else 0


# ------------------------------------------------------------------- check

def cmd_check(args):
    st = load_status()
    entries = {e["module"]: e for e in manifest()}
    errors = []
    unknown = [m for m in st["completed"] if m not in entries]
    errors += ["completed module is not a top-level ulib module: %s" % m for m in unknown]
    corpus = example_corpus()
    exported_names = set()
    for m in st["completed"]:
        if m not in entries:
            continue
        data = load_export(args.exports, m)
        if data is None:
            errors.append("%s: completed but not exported" % m)
            continue
        exported_names.update(d["name"] for d in data["declarations"])
        r = classify(m, data, st)
        errors += ["%s: undocumented %s" % (m, n) for n in r["missing"]]
        errors += ["%s: %s" % (m, p) for p in lint_module(data, corpus)]
        if audit_module(entries[m]) and m not in st["unsupported"]:
            errors.append("%s: candidate unsupported public forms (see `audit`) "
                          "are not recorded in the status file" % m)
    for m, why in st["blocked"].items():
        if m in st["completed"]:
            errors.append("%s: both completed and blocked" % m)
        if m not in entries:
            errors.append("blocked module is not a top-level ulib module: %s" % m)
        if not why.strip():
            errors.append("blocked module without a reason: %s" % m)
    for name, why in st["exclusions"].items():
        mod = name.rsplit(".", 1)[0]
        if not why.strip():
            errors.append("exclusion without a reason: %s" % name)
        if mod in st["completed"] and name not in exported_names:
            errors.append("stale exclusion, not exported: %s" % name)
    if getattr(args, "complete", False):
        done = set(st["completed"]) | set(st["blocked"])
        errors += ["%s: neither completed nor blocked" % m
                   for m in sorted(entries) if m not in done]
    for e in errors:
        print(e)
    print("%d completed modules checked, %d problems" % (len(st["completed"]), len(errors)))
    return 1 if errors else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("manifest")

    p = sub.add_parser("export")
    p.add_argument("--fstar", required=True)
    p.add_argument("--cache", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--module", action="append", default=[])

    p = sub.add_parser("audit")
    p.add_argument("--module", action="append", default=[])

    p = sub.add_parser("coverage")
    p.add_argument("--exports", required=True)
    p.add_argument("--module", action="append", default=[])
    p.add_argument("--json")
    p.add_argument("-v", "--verbose", action="store_true")

    p = sub.add_parser("lint")
    p.add_argument("--exports", required=True)
    p.add_argument("--module", action="append", default=[])

    p = sub.add_parser("lint-file")
    p.add_argument("files", nargs="+")

    p = sub.add_parser("lint-source")
    p.add_argument("files", nargs="+")

    p = sub.add_parser("check")
    p.add_argument("--exports", required=True)
    p.add_argument("--complete", action="store_true",
                   help="also require every top-level module to be completed or blocked")

    args = ap.parse_args()
    if args.cmd == "manifest":
        for e in manifest():
            print("%-48s %-52s%s" % (e["module"], e["source"],
                                     "  generated" if e["generated"] else ""))
        return 0
    return {"export": cmd_export, "audit": cmd_audit, "coverage": cmd_coverage,
            "lint": cmd_lint, "lint-file": cmd_lint_file,
            "lint-source": cmd_lint_source, "check": cmd_check}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
