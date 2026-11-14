#!/usr/bin/env python3
"""G10 (generic → §S) fixtures for reach_outage.py: `python3 -m unittest tools/test_reach_outage.py`.

Each case commits fixtures/g10/Stock.lean (the root and the §S declaration `stock_helper`) and one
case file to a throwaway git repo under ConsensusLean/Fixture/, runs reach_outage.py on it at HEAD
and checks the `[deps] generic → §S violations: N` line.
"""
import os, re, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
FIX = os.path.join(HERE, "fixtures", "g10")
GIT = ["git", "-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid", "-c", "commit.gpgsign=false"]


def scan(case, extra_s="", *flags):
    with tempfile.TemporaryDirectory() as repo:
        os.makedirs(os.path.join(repo, "ConsensusLean", "Fixture"))
        for src, dst in (("Stock.lean", "Stock.lean"), (case, "Case.lean")):
            with open(os.path.join(FIX, src)) as i, open(os.path.join(repo, "ConsensusLean", "Fixture", dst), "w") as o:
                o.write(i.read())
        with open(os.path.join(FIX, "sectionS.md")) as i, open(os.path.join(repo, "sectionS.md"), "w") as o:
            o.write(i.read() + extra_s)
        for cmd in (["init", "-q"], ["add", "ConsensusLean"], ["commit", "-qm", "fixture"]):
            subprocess.run(GIT + cmd, cwd=repo, check=True, capture_output=True)
        r = subprocess.run([sys.executable, os.path.join(HERE, "reach_outage.py"), "--repo", repo,
                            "--rev", "HEAD", "--root", "fixture_root", "--static-only",
                            "--section-s", os.path.join(repo, "sectionS.md"), *flags],
                           capture_output=True, text=True)
    assert "§S entries not at a declaration line" not in r.stdout, r.stdout
    return r.returncode, r.stdout


def count(out, title):
    n = re.search(r"^\[" + title + r": (\d+)$", out, re.M)
    assert n, out
    k = out.index(n.group(0)) + len(n.group(0)) + 1
    items = re.findall(r"^    (.+)$", out[k:].split("\n[", 1)[0], re.M)
    return int(n.group(1)), items


def g10(case):
    """(violations, edges, exit code) of the generic → §S check on `case`."""
    rc, out = scan(case)
    n, items = count(out, r"deps\] generic → §S violations")
    return n, [tuple(re.findall(r"(\S+) @ \S+", e)) for e in items], rc


class G10(unittest.TestCase):
    def test_a_stock_before_generic_section(self):
        self.assertEqual(g10("a_stock_before_section.lean"), (0, [], 0))

    def test_b_generic_in_section_calls_section_s(self):
        self.assertEqual(g10("b_generic_in_section.lean"), (1, [("Fx.b_generic", "Fx.stock_helper")], 1))

    def test_c_stock_after_section_end(self):
        self.assertEqual(g10("c_stock_after_section.lean"), (0, [], 0))

    def test_d_local_setup_binder_shadows_section(self):
        self.assertEqual(g10("d_local_setup_binder.lean"), (0, [], 0))


class CheckSectionS(unittest.TestCase):
    def test_flags_entry_without_stock_marker(self):
        # Case.lean:12 is `a_generic`, under the section's `variable (S : BoundSetup)`.
        _, out = scan("a_stock_before_section.lean", "- `a_generic` — ConsensusLean/Fixture/Case.lean:12\n",
                      "--check-section-s")
        n, items = count(out, r"check\] §S entries without a stock marker")
        self.assertEqual((n, [i.split()[0] for i in items]), (1, ["Fx.a_generic"]))


if __name__ == "__main__":
    unittest.main()
