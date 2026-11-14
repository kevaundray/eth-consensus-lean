#!/usr/bin/env python3
"""reach_outage.py — static forward-reachability over Lean declarations at a git revision.

Read-only. Reads files only via `git show <rev>:<path>` / `git ls-tree`; never touches the
working tree. Used for C2 plan rev 3 §0.4 and gate G7.

Usage:
  python3 reach_outage.py --repo /home/kev/work/ecl-committee-local --rev 9124d968 \
      --root outage_protected_at --section-s sectionS.md --static-only \
      --query Consensus.Goldilocks.Compose.vote_extends \
      --query Consensus.Goldilocks.Compose.Growing.vote_extends \
      [--dump reach.txt] [--grep-stock]

Fail-closed: exits 1 without --section-s, with an empty §S list, an entry not at a declaration
line, a generic → §S edge or a §S declaration reachable from --root, and without --g7-elab unless
--static-only (a diagnostic run that certifies nothing). Reads ConsensusLean/ and Solution.lean.

  --root   suffix of the root declaration's full name (matched as '.<root>' or exact)
  --query  full (or suffix) declaration names; membership is reported for both closures
  --dump   write the reachable set (mode, full name, file:line) to a file
  --grep-stock  (G7) list reached declarations whose body contains .stock / hstock /
                `committeeSize = sp.n`
  --g7-elab WORKTREE  (G7(i) refined, c56-2325) dump the reached set (--g7-mode closure, default
                by-name) and check it on ELABORATED constants: runs G7Check.lean (next to this
                file, or --g7-script) with `lake env lean` in WORKTREE under the build lock
                (`flock /tmp/dc-lean-build.lock env LEAN_NUM_THREADS=2`). Needs --section-s. The
                reach is computed at --rev from git; the constants come from WORKTREE's built
                `.lake`, which is --rev only when WORKTREE is clean and built.
                Two-step equivalent:
                  reach_outage.py … --dump reach.txt
                  G7_NAMES=reach.txt G7_SECTION_S=sectionS.md [G7_MODE=by-name] \\
                    flock /tmp/dc-lean-build.lock env LEAN_NUM_THREADS=2 \\
                    lake env lean G7Check.lean        # from WORKTREE

Two closures are computed:
  by-name : tokens resolved namespace-aware (innermost enclosing namespace first, then the
            file's `open`s, then qualified-suffix match); dot calls on terms (`h.foo`) ignored.
            This is an under-approximation of dot-notation calls.
  +dots   : additionally resolves `h.foo` to every declaration `T.foo` where `T` is itself a
            declared name (a type namespace). Over-approximation (field-name collisions).
Stripped before tokenizing: `/- ... -/` blocks (incl. docstrings), `--` comments, structure
field declarations (`  name :`), and `name :=` named fields.

Caveat: static name analysis, not elaboration. Review any surprising hit by hand.
Counts at 9124d968, root outage_protected_at: by-name 1488, +dots 2293.
"""
import argparse, collections, os, re, subprocess, sys, tempfile
from collections import deque

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |public |noncomputable |nonrec )*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)", re.M)
TOK = re.compile(r"(?<![\w.'])([A-Za-z_][\w'!?₀-₉]*(?:\.[A-Za-z_][\w'!?₀-₉]*)*)")
SCOPE_OPEN = re.compile(r"^(?:(?:noncomputable|public|private|meta)\s+)*section\b|^namespace\s|^mutual\b")
BINDER = re.compile(r"[({]([^(){}:]*):([^(){}]*)[)}]")
S_TOK = re.compile(r"(?<![\w.'])S(?![\w'])")


def git(repo, *args):
    return subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True, check=True).stdout


def load(repo, rev):
    files = [l for l in git(repo, "ls-tree", "-r", "--name-only", rev, "--", "ConsensusLean", "Solution.lean").split()
             if l.endswith(".lean")]
    return {f: git(repo, "show", f"{rev}:{f}") for f in files}


def index(src, open_prefixes=False):
    decls, fullname, opens, nsline = {}, {}, collections.defaultdict(set), {}
    for f, t in src.items():
        L = t.split("\n")
        idx = [(i, DECL.match(l).group(1)) for i, l in enumerate(L) if DECL.match(l)]
        for k, (i, n) in enumerate(idx):
            j = idx[k + 1][0] if k + 1 < len(idx) else len(L)
            decls[(f, i + 1)] = (n, "\n".join(L[i:j]))
        stack, arr = [], []
        for i, l in enumerate(L):
            m = re.match(r"^namespace\s+(\S+)", l)
            if m:
                stack.append(m.group(1).split(".")); arr.append(".".join(c for s in stack for c in s)); continue
            if re.match(r"^section\b", l):
                stack.append([]); arr.append(".".join(c for s in stack for c in s)); continue
            if re.match(r"^end\b", l) and stack:
                stack.pop(); arr.append(".".join(c for s in stack for c in s)); continue
            cur = ".".join(c for s in stack for c in s)
            m = re.match(r"^open\s+(.*)", l)
            if m:
                for o in re.findall(r"[A-Z][\w.]*", m.group(1).split(" in")[0]):
                    opens[f].add(o)
                    if cur:
                        opens[f].add(cur + "." + o)
                    if open_prefixes and cur:
                        parts = cur.split(".")
                        for k in range(1, len(parts)):
                            opens[f].add(".".join(parts[:k]) + "." + o)
            if (f, i + 1) in decls:
                n = decls[(f, i + 1)][0].removeprefix("_root_.")
                fullname[(f, i + 1)] = (cur + "." + n) if cur else n
            arr.append(cur)
        nsline[f] = arr
    bylast = collections.defaultdict(list)
    for k, fn in fullname.items():
        bylast[fn.split(".")[-1]].append(k)
    fns = set(fullname.values())
    dotlast = collections.defaultdict(list)
    for k, fn in fullname.items():
        if fn.rsplit(".", 1)[0] in fns:
            dotlast[fn.split(".")[-1]].append(k)
    return decls, fullname, opens, nsline, bylast, dotlast


def make_resolver(fullname, opens, nsline, bylast):
    def resolve(f, line, tokn):
        cands = bylast.get(tokn.split(".")[-1], [])
        if not cands:
            return []
        cur = nsline[f][line - 1] if line - 1 < len(nsline[f]) else ""
        parts = cur.split(".") if cur else []
        for p in [".".join(parts[:k]) for k in range(len(parts), -1, -1)]:
            full = (p + "." + tokn) if p else tokn
            hit = [k for k in cands if fullname[k] == full]
            if hit:
                same = [k for k in hit if k[0] == f]
                return same or hit
        hit = []
        for o in opens[f]:
            hit += [k for k in cands if fullname[k] == o + "." + tokn]
        if hit:
            return hit
        if "." in tokn:
            return [k for k in cands if fullname[k].endswith("." + tokn)]
        return []
    return resolve


def make_fwd(decls, resolve, dotlast):
    def fwd(key, dots):
        f, l = key
        body = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), decls[key][1], flags=re.S)
        out = set()
        for i, line in enumerate(body.split("\n")):
            line = re.sub(r"--.*", "", line)
            for m in TOK.finditer(line):
                t, rest = m.group(1), line[m.end():]
                if re.match(r"\s*:=", rest) and "." not in t:
                    continue
                if i > 0 and re.match(r"^\s+" + re.escape(t) + r"\s*:(?!=)", line):
                    continue
                first = t.split(".")[0]
                if "." in t and first[:1].islower():
                    if dots:
                        out.update(dotlast.get(t.split(".")[-1], []))
                else:
                    out.update(resolve(f, l + i, t))
        out.discard(key)
        return out
    return fwd


def reach(fullname, fwd, root, dots):
    start = [k for k, fn in fullname.items() if fn == root or fn.endswith("." + root)]
    par = {k: None for k in start}
    q = deque(start)
    while q:
        k = q.popleft()
        for x in fwd(k, dots):
            if x not in par:
                par[x] = k
                q.append(x)
    return start, par


def path(par, k, fullname):
    out = []
    while k:
        out.append(f"{fullname[k]} @ {k[0]}:{k[1]}")
        k = par[k]
    return out


def s_binder(text):
    """Type of the last `(S : T)` / `{S : T}` binder in `text`, or None if `text` binds no `S`."""
    ty = None
    for names, t in BINDER.findall(text):
        if "S" in names.split():
            ty = t.strip()
    return ty


def s_scope(text):
    """Per 0-based line of `text`: the type of the `variable` binding of `S` in scope, or None.

    Scopes follow source order: `section`/`namespace`/`mutual` open one, `end` closes the innermost
    and drops the `variable`s declared in it; a later `variable` binding `S` shadows an earlier one
    in the same or an enclosing scope. Comments are blanked first (line numbers kept)."""
    L = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S).split("\n")
    L = [re.sub(r"--.*", "", l) for l in L]
    stack, out, i = [None], [], 0
    while i < len(L):
        j = i + 1
        if SCOPE_OPEN.match(L[i]):
            stack.append(None)
        elif re.match(r"^end\b", L[i]) and len(stack) > 1:
            stack.pop()
        elif re.match(r"^variable\b", L[i]):
            while j < len(L) and re.match(r"[ \t]+\S", L[j]):
                j += 1
            ty = s_binder("\n".join(L[i:j]))
            if ty is not None:
                stack[-1] = ty
        out += [next((t for t in reversed(stack) if t is not None), None)] * (j - i)
        i = j
    return out


STOCK = re.compile(r"\bhstock\b|committeeSize\s*=|⟨S, stock⟩")


def header(decl):
    """A declaration's header, comments stripped: up to the first `:=` outside brackets (`(sp := sp)`
    is a named argument); a `Prop` definition states its premises in its body, so it is read whole."""
    text = re.sub(r"--.*", "", re.sub(r"/-.*?-/", "", decl, flags=re.S))
    depth, end = 0, len(text)
    for m in re.finditer(r"[([{⟨]|[)\]}⟩]|:=", text):
        if m.group() == ":=" and depth == 0:
            end = m.start()
            break
        depth += 0 if m.group() == ":=" else (1 if m.group() in "([{⟨" else -1)
    return (text if re.search(r":\s*Prop\s*$", text[:end]) else text[:end]).rstrip()


def stock_marker(decl, scope_ty):
    """The stock marker of a declaration's header, or None: `hstock`, `committeeSize =`,
    `⟨S, stock⟩`, or `S` bound to `Setup` by a header binder or (`scope_ty`) the in-scope `variable`."""
    head = header(decl)
    m, ty = STOCK.search(head), s_binder(head)
    if m:
        return m.group()
    if ty == "Setup":
        return "(S : Setup)"
    if ty is None and S_TOK.search(head) and scope_ty == "Setup":
        return "variable (S : Setup)"
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", required=True)
    ap.add_argument("--rev", required=True)
    ap.add_argument("--root", default="outage_protected_at")
    ap.add_argument("--query", action="append", default=[])
    ap.add_argument("--dump")
    ap.add_argument("--grep-stock", action="store_true")
    ap.add_argument("--open-prefixes", action="store_true",
                    help="resolve `open X` inside `namespace A.B` also as A.B.X and A.X (Lean semantics)")
    ap.add_argument("--setup-binders", action="store_true",
                    help="(G7 widened) list reached declarations with a `Setup` binder in their header, "
                         "or using `S` in a file with a `variable … (S : Setup)` line")
    ap.add_argument("--section-s",
                    help="(G7(ii) dependency check) markdown/text file listing §S declarations as "
                         "`name` — path:line; reports every generic declaration (a `BoundSetup` binder "
                         "in its header, `S` in its header under an in-scope `variable (S : BoundSetup)` "
                         "and no local `S` binder, or any non-§S declaration under --generic-dir) that "
                         "depends directly on a §S declaration, and any §S declaration reachable from --root")
    ap.add_argument("--generic-dir", action="append", default=[],
                    help="path prefix of the generic S/GS files (repeatable)")
    ap.add_argument("--check-section-s", action="store_true",
                    help="with --section-s: list §S entries whose header at --rev has no stock marker "
                         "(`hstock`, `committeeSize =`, `⟨S, stock⟩`, or `S` bound to `Setup` by a header "
                         "binder or the in-scope `variable`)")
    ap.add_argument("--g7-elab", metavar="WORKTREE",
                    help="(G7(i) refined) run G7Check.lean on the dumped reached set in WORKTREE")
    ap.add_argument("--g7-script",
                    default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "G7Check.lean"))
    ap.add_argument("--g7-mode", default="by-name", choices=["by-name", "+dots"])
    ap.add_argument("--static-only", action="store_true",
                    help="diagnostic only: do not certify the elaborated G7 gate")
    a = ap.parse_args()

    if not a.section_s:
        print("G7 failed: --section-s is required")
        return 1
    if not a.static_only and not a.g7_elab:
        print("G7 failed: combined gate requires --g7-elab; use --static-only for diagnostics")
        return 1
    failed = False
    src = load(a.repo, a.rev)
    decls, fullname, opens, nsline, bylast, dotlast = index(src, a.open_prefixes)
    fwd = make_fwd(decls, make_resolver(fullname, opens, nsline, bylast), dotlast)
    print(f"rev={a.rev} files={len(src)} decls={len(decls)}")
    res = {}
    for mode, dots in (("by-name", False), ("+dots", True)):
        start, par = reach(fullname, fwd, a.root, dots)
        res[mode] = par
        print(f"[{mode}] roots={[fullname[k] for k in start]} reachable={len(par)}")
    for qn in a.query:
        ks = [k for k, fn in fullname.items() if fn == qn or fn.endswith("." + qn)]
        if not ks:
            print(f"query {qn}: NOT FOUND")
        for k in ks:
            for mode, par in res.items():
                print(f"query {fullname[k]} @ {k[0]}:{k[1]} [{mode}]: {'REACHED' if k in par else 'not reached'}")
                if k in par:
                    for step in path(par, k, fullname):
                        print(f"    {step}")
    dump = a.dump
    if a.g7_elab and not dump:
        dump = tempfile.NamedTemporaryFile("w", suffix=".txt", prefix="g7-reach-", delete=False).name
    if dump:
        with open(dump, "w") as fh:
            for mode, par in res.items():
                for k in sorted(par):
                    fh.write(f"{mode}\t{fullname[k]}\t{k[0]}:{k[1]}\n")
        print(f"dumped to {dump}")
    if a.grep_stock:
        pat = re.compile(r"\.stock\b|\bhstock\b|committeeSize = sp\.n")
        for mode, par in res.items():
            hits = [k for k in par if pat.search(re.sub(r"/-.*?-/", "", decls[k][1], flags=re.S))]
            print(f"[{mode}] G7 stock hits: {len(hits)}")
            for k in sorted(hits):
                print(f"    {fullname[k]} @ {k[0]}:{k[1]}")
    if a.setup_binders:
        hdr = re.compile(r"[({]\s*[^(){}:]*:\s*Setup\s*[)}]")
        varf = {f for f, t in src.items()
                if any(re.search(r"[({]\s*S\s*:\s*Setup\s*[)}]", blk)
                       for blk in re.findall(r"^variable\b[^\n]*(?:\n[ \t]+[^\n]*)*", t, re.M))}
        for mode, par in res.items():
            hits = []
            for k in par:
                body = re.sub(r"/-.*?-/", "", decls[k][1], flags=re.S)
                head = body.split(":=", 1)[0]
                if hdr.search(head):
                    hits.append((k, "binder"))
                elif k[0] in varf and re.search(r"(?<![\w.'])S(?![\w'])", head):
                    hits.append((k, "variable"))
            print(f"[{mode}] G7 Setup-binder hits: {len(hits)}")
            for k, why in sorted(hits):
                print(f"    {fullname[k]} @ {k[0]}:{k[1]} ({why})")

    if a.section_s:
        sec = set()
        for line in open(a.section_s):
            m = re.search(r"`([^`]+)`\s*[—-]+\s*(\S+):(\d+)", line)
            if m:
                sec.add((m.group(2), int(m.group(3))))
        if not sec:
            print("G7 failed: §S list is empty")
            return 1
        missing = [k for k in sec if k not in decls]
        if missing:
            print(f"§S entries not at a declaration line: {sorted(missing)}")
            failed = True
        fwd0 = make_fwd(decls, make_resolver(fullname, opens, nsline, bylast), dotlast)
        bound = re.compile(r"[({]\s*[^(){}:]*:\s*BoundSetup\s*[)}]")
        scope = {f: s_scope(t) for f, t in src.items()}
        heads = {k: re.sub(r"/-.*?-/", "", body, flags=re.S).split(":=", 1)[0] for k, (_, body) in decls.items()}
        viol = []
        for k in decls:
            if k in sec:
                continue
            head = heads[k]
            generic = (any(k[0].startswith(g) for g in a.generic_dir) or bool(bound.search(head))
                       or (scope[k[0]][k[1] - 1] == "BoundSetup" and S_TOK.search(head)
                           and s_binder(head) is None))
            if not generic:
                continue
            for d in fwd0(k, False):
                if d in sec:
                    viol.append((k, d))
        print(f"[deps] generic → §S violations: {len(viol)}")
        failed = failed or bool(viol)
        for k, d in sorted(viol):
            print(f"    {fullname[k]} @ {k[0]}:{k[1]}  →  {fullname[d]} @ {d[0]}:{d[1]}")
        for mode, par in res.items():
            hit = sorted(k for k in sec if k in par)
            print(f"[{mode}] §S declarations reachable from root: {len(hit)}")
            failed = failed or bool(hit)
            for k in hit:
                print(f"    {fullname[k]} @ {k[0]}:{k[1]}")
        if a.check_section_s:
            bad = sorted(k for k in sec if k in decls and not stock_marker(decls[k][1], scope[k[0]][k[1] - 1]))
            print(f"[check] §S entries without a stock marker: {len(bad)}")
            for k in bad:
                print(f"    {fullname[k]} @ {k[0]}:{k[1]}")

    if a.g7_elab:
        if not a.section_s:
            ap.error("--g7-elab needs --section-s")
        dirty = git(a.g7_elab, "status", "--porcelain", "--untracked-files=no", "--", "ConsensusLean")
        head = git(a.g7_elab, "rev-parse", "--short", "HEAD").strip()
        print(f"[g7-elab] reach at rev={a.rev}; constants from built .lake of {a.g7_elab} "
              f"(HEAD {head}, {'DIRTY: ' + str(len(dirty.splitlines())) + ' modified files' if dirty else 'clean'})",
              flush=True)
        env = dict(os.environ, G7_NAMES=dump, G7_SECTION_S=os.path.abspath(a.section_s), G7_MODE=a.g7_mode)
        r = subprocess.run(["flock", "/tmp/dc-lean-build.lock", "env", "LEAN_NUM_THREADS=2",
                            "lake", "env", "lean", a.g7_script], cwd=a.g7_elab, env=env)
        if r.returncode:
            return r.returncode
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
