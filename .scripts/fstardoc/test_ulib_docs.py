"""Tests for ulib_docs.py: run with `python3 test_ulib_docs.py`."""
import contextlib
import io
import json
import os
import shutil
import sys
import tempfile
import unittest
from types import SimpleNamespace

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ulib_docs as u  # noqa: E402


def decl(name, kind="val", doc=None):
    return {"name": name, "kind": kind, "doc": doc}


class SourceDocs(unittest.TestCase):
    """source_docs must read payloads as the lexer does (DocsSugar.fst)."""

    def docs(self, text):
        return list(u.source_docs(text))

    def test_dedent_and_trim(self):
        src = "(*|  First line.\n\n    Indented   \n      more\n *)\nval x : int\n"
        self.assertEqual(self.docs(src), [(1, ["First line.", "", "Indented", "  more"])])

    def test_nested_comment_kept(self):
        src = "(*| Uses (* nested *) comments. *)\n"
        self.assertEqual(self.docs(src), [(1, ["Uses (* nested *) comments."])])

    def test_line_numbers(self):
        src = "module M\n\n(* (*| not a doc *) *)\n// (*| nor this\nlet s = \"(*|\"\n(*| Doc. *)\n"
        self.assertEqual(self.docs(src), [(6, ["Doc."])])


class Gates(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.exports = os.path.join(self.tmp, "exports")
        self.examples = os.path.join(self.tmp, "examples")
        os.makedirs(self.exports)
        os.makedirs(self.examples)
        self.status = {"completed": ["FStar.Option"], "exclusions": {},
                       "unsupported": {}, "blocked": {}}
        self.saved = (u.load_status, u.EXAMPLES_DIR)
        u.load_status = lambda: self.status
        u.EXAMPLES_DIR = self.examples

    def tearDown(self):
        u.load_status, u.EXAMPLES_DIR = self.saved
        shutil.rmtree(self.tmp)

    def export(self, decls, module="FStar.Option"):
        with open(os.path.join(self.exports, module + ".json"), "w") as f:
            json.dump({"declarations": decls}, f)

    def check(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            rc = u.cmd_check(SimpleNamespace(exports=self.exports))
        return rc, out.getvalue()

    def test_complete_module_passes(self):
        self.export([decl("FStar.Option.get", doc=["Returns the value."]),
                     decl("FStar.Option.Some", kind="constructor")])
        self.assertEqual(self.check(), (0, "1 completed modules checked, 0 problems\n"))

    def test_undocumented_declaration_fails(self):
        self.export([decl("FStar.Option.get")])
        rc, out = self.check()
        self.assertEqual(rc, 1)
        self.assertIn("undocumented FStar.Option.get", out)

    def test_excluded_declaration_passes(self):
        self.status["exclusions"]["FStar.Option.get"] = "Internal helper."
        self.export([decl("FStar.Option.get")])
        self.assertEqual(self.check()[0], 0)

    def test_exclusion_needs_reason_and_must_exist(self):
        self.status["exclusions"]["FStar.Option.gone"] = " "
        self.export([decl("FStar.Option.get", doc=["Returns the value."])])
        rc, out = self.check()
        self.assertEqual(rc, 1)
        self.assertIn("exclusion without a reason: FStar.Option.gone", out)
        self.assertIn("stale exclusion, not exported: FStar.Option.gone", out)

    def test_missing_export_fails(self):
        self.assertIn("FStar.Option: completed but not exported", self.check()[1])

    def test_unknown_completed_module_fails(self):
        self.status["completed"].append("FStar.NoSuchModule")
        self.export([decl("FStar.Option.get", doc=["Returns the value."])])
        self.assertIn("not a top-level ulib module: FStar.NoSuchModule", self.check()[1])

    def test_lint_problem_fails(self):
        self.export([decl("FStar.Option.get", doc=["Uses [legacy] references."])])
        self.assertIn("FStar.Option.get, doc line 1", self.check()[1])

    def test_examples_must_be_checked(self):
        doc = ["Example:", "", "```fstar", "let x = 1", "```"]
        self.export([decl("FStar.Option.get", doc=doc)])
        self.assertIn("not found verbatim", self.check()[1])
        with open(os.path.join(self.examples, "Ex.fst"), "w") as f:
            f.write("module Ex\n\nlet x = 1\n")
        self.assertEqual(self.check()[0], 0)

    def test_text_fence_is_not_checked(self):
        doc = ["```text", "let x = 1", "```"]
        self.export([decl("FStar.Option.get", doc=doc)])
        self.assertEqual(self.check()[0], 0)

    def test_blocked_module_cannot_be_completed(self):
        self.status["blocked"]["FStar.Option"] = "Reason."
        self.export([decl("FStar.Option.get", doc=["Returns the value."])])
        self.assertIn("FStar.Option: both completed and blocked", self.check()[1])

    def test_coverage_counts(self):
        self.status["exclusions"]["FStar.Option.b"] = "Reason."
        r = u.classify("FStar.Option", {"declarations": [
            decl("FStar.Option.a", doc=["A."]), decl("FStar.Option.b"),
            decl("FStar.Option.c"), decl("FStar.Option.C", kind="constructor")]},
            self.status)
        self.assertEqual((r["eligible"], r["documented"], r["excluded"],
                          r["constructors"], r["missing"]),
                         (3, 1, 1, 1, ["FStar.Option.c"]))


if __name__ == "__main__":
    unittest.main()
