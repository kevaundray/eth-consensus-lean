"""Fixtures of scripts/stock-reach.py (scripts/fixtures/stock-reach).

Static cases: each commits fixtures/stock-reach/Stock.lean (the setup, `stock` and the listed
`stock_helper`) and one case file to a throwaway repository under ConsensusLean/Fixture/ (or, as a
generic directory, ConsensusLean/Fixture/Generic/) and checks the verdicts of the list, dirs, deps,
twins and reach checks.
"""
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True  # a self-test leaves no scripts/__pycache__ in the checkout

HERE = Path(__file__).resolve().parent
FIX = HERE / "fixtures" / "stock-reach"
GIT = ["git", "-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid", "-c", "commit.gpgsign=false"]
GENERIC = "ConsensusLean/Fixture/Generic/"


def scan(case=None, generic=False, list_text=None, extra=(), roots=("fixture_root",), more=()):
    """Run stock-reach.py on Stock.lean plus `case` (as Case.lean) and `more` (under their own names);
    return (exit status, output)."""
    with tempfile.TemporaryDirectory() as repo:
        files = {"ConsensusLean/Fixture/Stock.lean": "Stock.lean"}
        if case:
            files[(GENERIC if generic else "ConsensusLean/Fixture/") + "Case.lean"] = case
        for m in more:
            files["ConsensusLean/Fixture/" + m] = m
        for dst, src in files.items():
            os.makedirs(os.path.dirname(os.path.join(repo, dst)), exist_ok=True)
            Path(repo, dst).write_text((FIX / src).read_text())
        Path(repo, "list.txt").write_text((FIX / "list.txt").read_text() if list_text is None else list_text)
        for cmd in (["init", "-q"], ["add", "ConsensusLean"], ["commit", "-qm", "fixture"]):
            subprocess.run(GIT + cmd, cwd=repo, check=True, capture_output=True)
        args = [sys.executable, "-I", str(HERE / "stock-reach.py"), "--repo", repo, "--rev", "HEAD",
                "--list", os.path.join(repo, "list.txt"), "--generic-dir", GENERIC]
        for r in roots:
            args += ["--root", r]
        r = subprocess.run(args + list(extra), capture_output=True, text=True, env=dict(os.environ, GIT_CONFIG_NOSYSTEM="1"))
    return r.returncode, r.stdout + r.stderr


def section(out, tag):
    """(count, items) of the `[tag] …: N` block of `out`; items are the declaration names."""
    m = re.search(r"^\[" + re.escape(tag) + r"\] [^\n]*: (\d+)$", out, re.M)
    assert m, out
    rest = out[m.end() + 1:].split("\n[", 1)[0]
    return int(m.group(1)), [l.split()[0] for l in re.findall(r"^    (\S.*)$", rest, re.M)]


def static(case, generic=False, **kw):
    return scan(case, generic, **kw)


class Scope(unittest.TestCase):
    """Each declaration is classified by its own binders and the `variable`s in scope it uses."""

    def test_sections_generic_deps(self):
        rc, out = static("sections.lean")
        self.assertEqual(section(out, "deps"), (4, ["Fx.before_section", "Fx.nested_generic",
                                                    "Fx.inside_generic", "Fx.after_section"]))
        self.assertEqual(rc, 1)

    def test_sections_stock_dirs(self):
        rc, out = static("sections.lean", generic=True)
        self.assertEqual(section(out, "dirs"), (2, ["Fx.inside_stock", "Fx.nested_stock"]))
        self.assertEqual(rc, 1)

    def test_multiline_variable(self):
        _, out = static("multiline.lean")
        self.assertEqual(section(out, "deps"), (1, ["Fx.only_S"]))
        _, out = static("multiline.lean", generic=True)
        self.assertEqual(section(out, "dirs"), (1, ["Fx.uses_hS"]))

    def test_local_shadowing(self):
        _, out = static("shadowing.lean")
        self.assertEqual(section(out, "deps"), (1, ["Fx.local_shadow"]))
        _, out = static("shadowing.lean", generic=True)
        self.assertEqual(section(out, "dirs"), (1, ["Fx.local_stock"]))

    def test_marker_edges(self):
        # a proof-only `{ S with vote := stock }` leaves a theorem generic; a definition's body,
        # `hstock` and a stock definition in the header make it stock; an unused `variable` is no binder
        _, out = static("edges.lean")
        self.assertEqual(section(out, "deps"), (1, ["Fx.body_only"]))
        _, out = static("edges.lean", generic=True)
        self.assertEqual(section(out, "dirs"), (3, ["Fx.def_body", "Fx.hstock_hyp", "Fx.via_def"]))

    def test_twins(self):
        rc, out = static("twins.lean")
        self.assertEqual(section(out, "twins"), (2, ["Fx.Other.stock_helper", "Fx.Scoped.stock_helper"]))
        self.assertEqual(rc, 1)

    def test_clean_passes(self):
        rc, out = static(None)
        self.assertEqual([section(out, t)[0] for t in ("dirs", "deps", "twins")], [0, 0, 0], out)
        self.assertEqual(rc, 0, out)


class StockList(unittest.TestCase):
    """The list fails closed: empty, unresolved, ambiguous and non-stock entries fail."""

    def check(self, text, case=None):
        rc, out = scan(case, list_text=text)
        return rc, out, section(out, "list")[1]

    def test_empty(self):
        rc, out, _ = self.check("# nothing\n")
        self.assertEqual(rc, 1, out)
        self.assertIn("    the list is empty", out)

    def test_unresolved(self):
        rc, out, items = self.check("ConsensusLean/Fixture/Stock.lean gone_helper\n")
        self.assertEqual((rc, len(items)), (1, 1), out)
        self.assertIn("gone_helper: 0 declarations", out)

    def test_not_stock(self):
        rc, out, _ = self.check("ConsensusLean/Fixture/Case.lean only_S\n", "multiline.lean")
        self.assertEqual(rc, 1, out)
        self.assertIn("is not stock (generic)", out)

    def test_ambiguous(self):
        rc, out, _ = self.check("ConsensusLean/Fixture/Case.lean stock_helper\n", "twins.lean")
        self.assertEqual(rc, 1, out)
        self.assertIn("stock_helper: 3 declarations", out)


REACH_LIST = (FIX / "list.txt").read_text() + "ConsensusLean/Fixture/Reach.lean B.foo\n"


class Reach(unittest.TestCase):
    """The reach verdict is the union of the static closures, so a name collision fails closed."""

    def test_shared_method_name_fails_closed(self):
        rc, out = scan(roots=["dots_root"], more=("Reach.lean",), list_text=REACH_LIST)
        self.assertRegex(out, r"(?m)^\[reach by-name\] Fx\.dots_root: reached=\d+ listed=0 stock=0$")
        # `a.foo` is followed to the listed `B.foo` too
        self.assertRegex(out, r"(?m)^\[reach \+dots\] Fx\.dots_root: reached=\d+ listed=1 stock=1$")
        self.assertIn("    listed Fx.B.foo @", out)
        self.assertEqual(rc, 1, out)


if __name__ == "__main__":
    unittest.main()
