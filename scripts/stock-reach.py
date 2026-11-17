#!/usr/bin/env python3
"""Stock-dependence check: the binding-generic Goldilocks results do not depend on a stock-only
declaration.

`Setup.vote` is the vote binding of a Goldilocks setup. A declaration is *stock* when it fixes the
binding to `stock`, *generic* when it binds a `Setup` and leaves the binding arbitrary. The roots
(binding-generic results; default `outage_protected_at` and `meetsObligations_persists_growing`)
and the generic directories must not depend on stock declarations. The stock-only list
(`scripts/stock-only.txt`) names the stock declarations that may sit among generic code; a
generic declaration must not use them.

Classification (source level, at --rev; comments removed first):
  header            the declaration up to its first `:=`, `where` or line-initial `|` outside
                    brackets (named arguments `(x := e)` stay inside); a `: Prop` definition is
                    read whole (it states its premises in its body). A declaration ends at the
                    next declaration or column-0 command (`variable`, `section`, `end`, `open`, …).
  classified text   the header of a `theorem`/`lemma` (its proof does not count), the whole text of
                    every other kind, after the `variable` binders in scope that the declaration
                    includes: those named in the classified text and not bound by its own binders,
                    those named by an `include` in scope, and, transitively, the variables named in
                    an included binder's type. Scopes follow source order: `section`, `namespace`
                    and `mutual` open one, `end` closes the innermost and drops its `variable`s and
                    `include`s; a later `variable` shadows an earlier binder of the same name;
                    `omit` removes an `include`; `variable … in` applies to the next declaration
                    only. (For a theorem this is its effective header.)
  stock marker      in the classified text, one of
                      `vote := stock`      (`{ S with vote := stock }`, a named argument)
                      `binding := stock`   (a named argument)
                      `vote = stock`       (a hypothesis on the binding)
                      `hstock`             (the stock-committee hypothesis name)
                      `committeeSize =`    (a hypothesis fixing the committee size)
                    `stock` may be qualified (`AsChainShape.stock`).
  Setup binder      a binder `(x : Setup)`, `{x : Setup}`, `⦃x : Setup⦄` (any qualification of
                    `Setup`) in the classified text.
  stock / generic   stock: a stock marker, or the classified text names a stock declaration that is
                    not a `theorem`/`lemma` (a stock structure or definition; reported `via <name>`);
                    generic: not stock, and a Setup binder.

Checks (each failure makes the exit status 1):
  list      the list is nonempty; every entry resolves to exactly one declaration of its name in
            its file, and that declaration is stock.
  dirs      every stock declaration under a --generic-dir is on the list.
  deps      no generic declaration, and no unlisted declaration under a --generic-dir, names a
            listed declaration (static, namespace-aware name resolution of its whole text).
  twins     no generic declaration outside an entry's file has the entry's (last-component) name.
  reach     (certifying; needs --elab) on the elaborated environment, the closure of each root
            over the constants of its type, value, constructors, recursor rules and primitive
            projections (StockReach.lean) contains no listed declaration, and no reached constant
            whose type binds a `Setup` uses `stock` or a listed declaration (in its type, value,
            constructors or its own auxiliary constants). The controls of
            StockReachControls.lean must give their expected verdicts.
Without --elab and without --static-only the run fails (nothing certifies the reach). With
--static-only the reach check is not run and the exit status covers the static checks only.

Diagnostics (never change the exit status):
  static reach   two source-level closures of each root: `by-name` resolves names namespace-aware
                 (innermost enclosing namespace, then the file's `open`s, then a qualified-suffix
                 match) and ignores dot calls on terms (`h.foo`), an under-approximation;
                 `+dots` also follows `h.foo` to every declaration `T.foo` of a declared `T`, an
                 over-approximation (two types sharing a method name). Each lists the listed and
                 the stock declarations it reaches. Not a verdict: the reach verdict is --elab's.
  --query        membership and path of named declarations in the static closures (and, with
                 --elab, in the elaborated ones).

Read-only on the repository: sources come from `git show <rev>:<path>`. --elab runs
`lake env lean` in --lake-dir (default --repo) on a driver composed of StockReachControls.lean
(or --elab-source files) and StockReach.lean; when those import anything it requires --lake-dir
to be clean at --rev, since the constants come from its build. Run it under your own lock when
other builds share the directory.

  python3 -I scripts/stock-reach.py --repo . --rev HEAD --elab
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict, deque

sys.dont_write_bytecode = True

HERE = os.path.dirname(os.path.abspath(__file__))
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|public|noncomputable|nonrec|partial|unsafe)\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)\s+([^\s(:{\[⦃]+)", re.M)
TOK = re.compile(r"(?<![\w.'])([A-Za-z_][\w'!?₀-₉]*(?:\.[A-Za-z_][\w'!?₀-₉]*)*)")
SCOPE_OPEN = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|public|private|meta)\s+)*section\b|^namespace\s|^mutual\b")
SETUP = re.compile(r"^(?:[\w.]*\.)?Setup$")
MARKERS = (
    ("vote := stock", r"\bvote\s*:=\s*(?:[\w.]*\.)?stock\b"),
    ("binding := stock", r"\bbinding\s*:=\s*(?:[\w.]*\.)?stock\b"),
    ("vote = stock", r"\bvote\s*=\s*(?:[\w.]*\.)?stock\b"),
    ("hstock", r"\bhstock\b"),
    ("committeeSize =", r"\bcommitteeSize\s*=(?!=)"),
)
MARKER = re.compile("|".join(f"(?:{p})" for _, p in MARKERS))
OPEN, CLOSE = "([{⦃⟨", ")]}⦄⟩"
DEFAULT_ROOTS = ["outage_protected_at", "meetsObligations_persists_growing"]
GENERIC_DIRS = ["ConsensusLean/Instances/Goldilocks/Lemmas/Simulation/",
                "ConsensusLean/Instances/Goldilocks/Lemmas/Growing/Simulation/"]


def git(repo, *args):
    return subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True, check=True).stdout


def load(repo, rev):
    files = [f for f in git(repo, "ls-tree", "-r", "--name-only", rev, "--", "ConsensusLean", "Solution.lean").split()
             if f.endswith(".lean")]
    return {f: git(repo, "show", f"{rev}:{f}") for f in files}


def strip_comments(text):
    """`text` with `/- … -/` blocks (nested) and `--` comments blanked; line numbers kept."""
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if two == "/-":
            depth += 1; i += 2; continue
        if depth and two == "-/":
            depth -= 1; i += 2; continue
        if depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1; continue
        if two == "--":
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(text[i]); i += 1
    return "".join(out)


def groups(text):
    """Top-level bracket groups of `text`: (opening bracket, inside)."""
    out, depth, start = [], 0, 0
    for i, c in enumerate(text):
        if c in OPEN:
            if depth == 0:
                start = i
            depth += 1
        elif c in CLOSE and depth:
            depth -= 1
            if depth == 0:
                out.append((text[start], text[start + 1:i]))
    return out


def split_binder(inside):
    """`names : type` of a binder group's inside, or None (instance binder, named argument)."""
    depth = 0
    for i, c in enumerate(inside):
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif c == ":" and depth == 0 and inside[i + 1:i + 2] != "=":
            names = inside[:i].split()
            if names and all(re.fullmatch(r"[\w'!?₀-₉]+", x) for x in names):
                return names, inside[i + 1:].strip()
            return None
    return None


def binders(text):
    """Typed binders `(names : type)`, `{…}`, `⦃…⦄` at the top level of `text`: [(name, type, source)]."""
    out = []
    for br, inside in groups(text):
        if br not in "({⦃":
            continue
        b = split_binder(inside)
        if b:
            out += [(x, b[1], f"{br}{inside}{CLOSE[OPEN.index(br)]}") for x in b[0]]
    return out


def header(decl):
    """A declaration's header (comments already stripped): up to the first `:=`, `where` or
    line-initial `|` outside brackets; a `: Prop` definition is read whole."""
    depth, end = 0, len(decl)
    for m in re.finditer(r"[([{⦃⟨]|[)\]}⦄⟩]|:=|\bwhere\b|\n\s*\|", decl):
        g = m.group()
        if g in OPEN:
            depth += 1
        elif g in CLOSE:
            depth -= 1
        elif depth == 0:
            end = m.start()
            break
    if decl[end:end + 2] == ":=" and re.search(r":\s*Prop\s*$", decl[:end]):
        return decl.rstrip()
    return decl[:end].rstrip()


def idents(text):
    return {m.group(1).split(".")[0] for m in TOK.finditer(text)}


class Scopes:
    """Per 0-based line of a comment-stripped file: the `variable` binders and `include`d names in
    scope (see the module docstring for the rules)."""

    def __init__(self, text):
        L = text.split("\n")
        stack = [({}, set())]          # per scope: name -> (type, source), included names
        pending = None                 # `variable … in` / `include … in` / `omit … in`
        self.at = []
        snap = None
        i = 0
        while i < len(L):
            j, line = i + 1, L[i]
            if re.match(r"^(variable|include|omit)\b", line):
                while j < len(L) and re.match(r"[ \t]+\S", L[j]):
                    j += 1
                blk = "\n".join(L[i:j])
                one = re.search(r"\bin\s*$", blk) is not None
                if one:
                    blk = re.sub(r"\bin\s*$", "", blk)
                if pending is None:
                    pending = ([dict(s[0]) for s in stack], [set(s[1]) for s in stack]) if one else None
                tgt_vars = pending[0][-1] if one else stack[-1][0]
                tgt_inc = pending[1] if one else [s[1] for s in stack]
                kw = line.split()[0]
                if kw == "variable":
                    for name, ty, src in binders(blk[len("variable"):]):
                        tgt_vars[name] = (ty, src)
                else:
                    names = [x for x in blk.split()[1:] if not x.startswith("[")]
                    for x in names:
                        if kw == "include":
                            tgt_inc[-1].add(x)
                        else:
                            for s in tgt_inc:
                                s.discard(x)
                snap = None
            elif SCOPE_OPEN.match(line):
                stack.append(({}, set())); snap = None
            elif re.match(r"^end\b", line) and len(stack) > 1:
                stack.pop(); snap = None
            if DECL.match(line) and pending is not None:
                cur = self._merge(pending[0], pending[1])
                pending = None
                self.at += [cur] * (j - i)
                snap = None
            else:
                if snap is None:
                    snap = self._merge([s[0] for s in stack], [s[1] for s in stack])
                self.at += [snap] * (j - i)
            i = j

    @staticmethod
    def _merge(varss, incs):
        v = {}
        for d in varss:
            v.update(d)
        return v, set().union(*incs)


def effective(kind, decl, scope):
    """The text a comment-stripped declaration is classified by: its header (its whole text unless
    it is a `theorem`/`lemma`) after the `variable` binders in `scope` it includes."""
    head = header(decl)
    after = head[DECL.match(head).end():] if DECL.match(head) else head
    own = {x for x, _, _ in binders(after)}
    vars_, inc = scope
    text = head if kind in ("theorem", "lemma") else decl
    todo = [x for x in (idents(text) | inc) if x in vars_ and x not in own]
    seen = {}
    while todo:
        x = todo.pop()
        if x in seen:
            continue
        seen[x] = vars_[x][1]
        todo += [y for y in idents(vars_[x][0]) if y in vars_ and y not in own and y not in seen]
    return "\n".join(seen.values()) + "\n" + text


def classify(eff, fullname, resolve):
    """Per declaration: ('stock', marker), ('generic', None) or (None, None). A declaration whose
    classified text names a stock definition (any kind but `theorem`/`lemma`) is stock too
    (`via <name>`)."""
    info, users = {}, defaultdict(set)
    for k, (_, text) in eff.items():
        m = MARKER.search(text)
        if m:
            info[k] = ("stock", m.group())
            continue
        info[k] = ("generic" if any(SETUP.match(ty) for _, ty, _ in binders(text)) else None, None)
        for t in set(TOK.findall(text)):
            if not ("." in t and t[:1].islower()):
                for d in resolve(k[0], k[1], t):
                    if d != k and eff[d][0] not in ("theorem", "lemma"):
                        users[d].add(k)
    todo = deque(k for k, (c, _) in info.items() if c == "stock")
    while todo:
        d = todo.popleft()
        for u in users.get(d, ()):
            if info[u][0] != "stock":
                info[u] = ("stock", f"via {fullname[d]}")
                todo.append(u)
    return info


COMMAND = re.compile(r"^(?:variable|include|omit|section|end|namespace|open|attribute|set_option|universe|export|"
                     r"mutual|#\w|local\s|scoped\s|deriving\s|initialize|notation|infix|prefix|postfix|macro|syntax|"
                     r"elab|@\[[^\]]*\]\s*(?:(?:public|noncomputable)\s+)*section|"
                     r"(?:(?:noncomputable|public|private|meta)\s+)+section)\b")


def index(src):
    """Declarations (each up to the next declaration or column-0 command), their classified texts,
    full names, opens and per-line namespaces of every file."""
    decls, fullname, opens, nsline, eff = {}, {}, defaultdict(set), {}, {}
    for f, raw in src.items():
        t = strip_comments(raw)
        L = t.split("\n")
        sc = Scopes(t)
        idx = [(i, DECL.match(l)) for i, l in enumerate(L) if DECL.match(l)]
        for k, (i, m) in enumerate(idx):
            j = idx[k + 1][0] if k + 1 < len(idx) else len(L)
            j = next((x for x in range(i + 1, j) if COMMAND.match(L[x])), j)
            body = "\n".join(L[i:j])
            decls[(f, i + 1)] = (m.group(2), body)
            eff[(f, i + 1)] = (m.group(1), effective(m.group(1), body, sc.at[i]))
        stack, arr = [], []
        for i, l in enumerate(L):
            m = re.match(r"^namespace\s+(\S+)", l)
            if m:
                stack.append(m.group(1).split(".")); arr.append(".".join(c for s in stack for c in s)); continue
            if SCOPE_OPEN.match(l):
                stack.append([]); arr.append(".".join(c for s in stack for c in s)); continue
            if re.match(r"^end\b", l) and stack:
                stack.pop(); arr.append(".".join(c for s in stack for c in s)); continue
            cur = ".".join(c for s in stack for c in s)
            m = re.match(r"^open\s+(.*)", l)
            if m:
                for o in re.findall(r"[A-Z][\w.]*", m.group(1).split(" in")[0]):
                    opens[f].add(o)
                    parts = cur.split(".") if cur else []
                    for k in range(1, len(parts) + 1):
                        opens[f].add(".".join(parts[:k]) + "." + o)
            if (f, i + 1) in decls:
                n = decls[(f, i + 1)][0].removeprefix("_root_.")
                fullname[(f, i + 1)] = (cur + "." + n) if cur and not decls[(f, i + 1)][0].startswith("_root_.") else n
            arr.append(cur)
        nsline[f] = arr
    bylast = defaultdict(list)
    for k, fn in fullname.items():
        bylast[fn.split(".")[-1]].append(k)
    fns = set(fullname.values())
    dotlast = defaultdict(list)
    for k, fn in fullname.items():
        if fn.rsplit(".", 1)[0] in fns:
            dotlast[fn.split(".")[-1]].append(k)
    return decls, fullname, opens, nsline, bylast, dotlast, eff


def make_resolver(fullname, opens, nsline, bylast):
    """Namespace-aware resolution of a name token at a file line to declarations."""
    def resolve(f, line, tok):
        cands = bylast.get(tok.split(".")[-1], [])
        if not cands:
            return []
        cur = nsline[f][line - 1] if line - 1 < len(nsline[f]) else ""
        parts = cur.split(".") if cur else []
        for p in [".".join(parts[:k]) for k in range(len(parts), -1, -1)]:
            full = (p + "." + tok) if p else tok
            hit = [k for k in cands if fullname[k] == full]
            if hit:
                return [k for k in hit if k[0] == f] or hit
        hit = [k for o in opens[f] for k in cands if fullname[k] == o + "." + tok]
        if hit:
            return hit
        return [k for k in cands if fullname[k].endswith("." + tok)] if "." in tok else []
    return resolve


def make_fwd(decls, resolve, dotlast):
    """Static references of a declaration (`dots`: also `h.foo` to every `T.foo`)."""
    memo = {}

    def fwd(key, dots):
        if (key, dots) in memo:
            return memo[key, dots]
        f, l = key
        out = set()
        for i, line in enumerate(decls[key][1].split("\n")):
            for m in TOK.finditer(line):
                t, rest = m.group(1), line[m.end():]
                if re.match(r"\s*:=", rest) and "." not in t:
                    continue                                  # a named argument or field
                if i > 0 and re.match(r"^\s+" + re.escape(t) + r"\s*:(?!=)", line):
                    continue                                  # a structure field declaration
                if "." in t and t.split(".")[0][:1].islower():
                    if dots:
                        out.update(dotlast.get(t.split(".")[-1], []))
                else:
                    out.update(resolve(f, l + i, t))
        out.discard(key)
        memo[key, dots] = out
        return out
    return fwd


def reach(fullname, fwd, starts, dots):
    par = {k: None for k in starts}
    q = deque(starts)
    while q:
        k = q.popleft()
        for x in fwd(k, dots):
            if x not in par:
                par[x] = k
                q.append(x)
    return par


def path(par, k, fullname):
    out = []
    while k:
        out.append(f"{fullname[k]} @ {k[0]}:{k[1]}")
        k = par[k]
    return list(reversed(out))


def read_list(path_):
    """Entries `<file> <name>` of the stock-only list (`#` comments, blank lines ignored)."""
    out = []
    for no, line in enumerate(open(path_), 1):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != 2 or not parts[0].endswith(".lean"):
            raise SystemExit(f"stock-reach: {path_}:{no}: expected `<file.lean> <name>`, got {line!r}")
        out.append((parts[0], parts[1]))
    return out


def resolve_entry(fullname, f, name):
    return [k for k, fn in fullname.items() if k[0] == f and (fn == name or fn.endswith("." + name))]


def compose(parts, core):
    """A Lean driver: the imports of every part first, then their bodies, then the core."""
    imports, bodies = [], []
    for p in parts + [core]:
        body = []
        for line in open(p):
            if re.match(r"^import\s", line):
                if line.strip() not in imports:
                    imports.append(line.strip())
            else:
                body.append(line)
        bodies.append("".join(body))
    return "\n".join(imports) + "\n" + "\n".join(bodies)


def run_elab(a, roots, listed, fullname, out):
    """The certifying reach check. Returns True when it passed."""
    lake_dir = os.path.abspath(a.lake_dir or a.repo)
    sources = a.elab_source if a.elab_source is not None else [os.path.join(HERE, "StockReachControls.lean")]
    imports = [l for p in sources for l in open(p) if re.match(r"^import\s", l)]
    if imports:
        head = git(lake_dir, "rev-parse", "HEAD").strip()
        want = git(a.repo, "rev-parse", a.rev).strip()
        dirty = git(lake_dir, "status", "--porcelain", "--untracked-files=no", "--", "ConsensusLean", "Solution.lean")
        if head != want or dirty:
            out(f"[reach] FAIL: the build in {lake_dir} is not --rev {want[:12]} "
                f"(HEAD {head[:12]}{', modified files' if dirty else ''}); the constants come from that build")
            return False
    with tempfile.TemporaryDirectory(prefix="stock-reach-") as tmp:
        drv = os.path.join(tmp, "StockReachDriver.lean")
        with open(drv, "w") as fh:
            fh.write(compose(sources, os.path.join(HERE, "StockReach.lean")))
        lst = os.path.join(tmp, "list.txt")
        with open(lst, "w") as fh:
            for f, k in listed:
                fh.write(f"{fullname[k]}\t{f[:-len('.lean')].replace('/', '.')}\n")
        env = dict(os.environ, SR_ROOTS=",".join(roots), SR_LIST=lst, SR_SETUP=a.setup_type,
                   SR_STOCK=",".join(a.stock_const), SR_PROJECT=",".join(a.project_prefix),
                   SR_CONTROLS=",".join(a.control), SR_QUERY=",".join(a.query))
        r = subprocess.run(["lake", "env", "lean", drv], cwd=lake_dir, env=env, capture_output=True, text=True)
    text = r.stdout + r.stderr
    for line in text.rstrip("\n").split("\n"):
        out(line)
    return r.returncode == 0 and re.search(r"^\[reach\] verdict: PASS$", text, re.M) is not None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", required=True, help="git repository to read the sources from")
    ap.add_argument("--rev", default="HEAD")
    ap.add_argument("--list", default=os.path.join(HERE, "stock-only.txt"), help="the stock-only list")
    ap.add_argument("--root", action="append", help="root declaration, full name or `.`-suffix (repeatable)")
    ap.add_argument("--generic-dir", action="append", help="path prefix of a generic directory (repeatable)")
    ap.add_argument("--query", action="append", default=[], help="report membership of this declaration")
    ap.add_argument("--static-only", action="store_true", help="skip the certifying reach check")
    ap.add_argument("--elab", action="store_true", help="run the certifying reach check (StockReach.lean)")
    ap.add_argument("--lake-dir", help="where to run `lake env lean` (default --repo)")
    ap.add_argument("--elab-source", action="append",
                    help="Lean file to prepend to the driver (default StockReachControls.lean; repeatable)")
    ap.add_argument("--setup-type", default="Consensus.Goldilocks.AsChainShape.Setup")
    ap.add_argument("--stock-const", action="append")
    ap.add_argument("--project-prefix", action="append", help="module prefix of the project (repeatable)")
    ap.add_argument("--control", action="append",
                    help="`name:+` (must be flagged) or `name:-` (must not); default the controls of "
                         "StockReachControls.lean")
    a = ap.parse_args()
    a.root = a.root or DEFAULT_ROOTS
    a.generic_dir = GENERIC_DIRS if a.generic_dir is None else a.generic_dir
    a.stock_const = a.stock_const or ["Consensus.Goldilocks.AsChainShape.stock"]
    a.project_prefix = a.project_prefix or ["ConsensusLean", "Solution"]
    a.control = a.control or ["StockReachCtrl.stock_use:+", "StockReachCtrl.generic_use:-",
                              "StockReachCtrl.setup_field:-"]
    failed = []
    out = print

    src = load(a.repo, a.rev)
    decls, fullname, opens, nsline, bylast, dotlast, eff = index(src)
    resolve = make_resolver(fullname, opens, nsline, bylast)
    fwd = make_fwd(decls, resolve, dotlast)
    info = classify(eff, fullname, resolve)
    out(f"rev={git(a.repo, 'rev-parse', '--short', a.rev).strip()} files={len(src)} decls={len(decls)}")
    counts = defaultdict(int)
    for c, _ in info.values():
        counts[c] += 1
    out(f"classification: stock={counts['stock']} generic={counts['generic']} other={counts[None]}")

    # list
    entries = read_list(a.list)
    listed, bad = [], []
    for f, name in entries:
        ks = resolve_entry(fullname, f, name)
        if len(ks) != 1:
            bad.append(f"{f} {name}: {len(ks)} declarations at the revision")
        elif info[ks[0]][0] != "stock":
            bad.append(f"{f} {name}: {fullname[ks[0]]} @ {ks[0][0]}:{ks[0][1]} is not stock "
                       f"({info[ks[0]][0] or 'no Setup binder'})")
        else:
            listed.append((f, ks[0]))
    if not entries:
        bad.append("the list is empty")
    out(f"[list] entries={len(entries)} resolved={len(listed)} unresolved or not stock: {len(bad)}")
    for b in bad:
        out(f"    {b}")
    if bad:
        failed.append("list")
    sec = {k for _, k in listed}

    def in_generic_dir(k):
        return any(k[0].startswith(g) for g in a.generic_dir)

    # dirs
    stray = sorted(k for k in decls if in_generic_dir(k) and info[k][0] == "stock" and k not in sec)
    out(f"[dirs] unlisted stock declarations under the generic directories: {len(stray)}")
    for k in stray:
        out(f"    {fullname[k]} @ {k[0]}:{k[1]} ({info[k][1]})")
    if stray:
        failed.append("dirs")

    # deps
    viol = []
    for k in decls:
        if k in sec or not (info[k][0] == "generic" or in_generic_dir(k)):
            continue
        viol += [(k, d) for d in fwd(k, False) if d in sec]
    out(f"[deps] generic → listed references: {len(viol)}")
    for k, d in sorted(viol):
        out(f"    {fullname[k]} @ {k[0]}:{k[1]}  →  {fullname[d]} @ {d[0]}:{d[1]}")
    if viol:
        failed.append("deps")

    # twins
    lastname = defaultdict(set)
    for f, k in listed:
        lastname[fullname[k].split(".")[-1]].add(f)
    twins = sorted(k for k in decls if info[k][0] == "generic" and k not in sec
                   and k[0] not in lastname.get(fullname[k].split(".")[-1], {k[0]}))
    out(f"[twins] generic declarations named like a listed one: {len(twins)}")
    for k in twins:
        out(f"    {fullname[k]} @ {k[0]}:{k[1]}")
    if twins:
        failed.append("twins")

    # static reach (diagnostic)
    starts, roots = [], []
    for r in a.root:
        ks = [k for k, fn in fullname.items() if fn == r or fn.endswith("." + r)]
        if len(ks) != 1:
            out(f"[root] {r}: {len(ks)} declarations")
            failed.append("root")
            continue
        starts.append(ks[0]); roots.append(fullname[ks[0]])
    for mode, dots in (("by-name", False), ("+dots", True)):
        for k0 in starts:
            par = reach(fullname, fwd, [k0], dots)
            hit = sorted(k for k in sec if k in par)
            stock = sorted(k for k in par if info[k][0] == "stock")
            out(f"[diagnostic static {mode}] {fullname[k0]}: reached={len(par)} listed={len(hit)} stock={len(stock)}")
            for k in hit:
                out(f"    listed {fullname[k]} @ {k[0]}:{k[1]}")
                for step in path(par, k, fullname):
                    out(f"        {step}")
            for k in stock:
                out(f"    stock {fullname[k]} @ {k[0]}:{k[1]} ({info[k][1]})")
            for q in a.query:
                for k in (k for k, fn in fullname.items() if fn == q or fn.endswith("." + q)):
                    out(f"    query {fullname[k]}: {'REACHED' if k in par else 'not reached'}")
                    if k in par:
                        for step in path(par, k, fullname):
                            out(f"        {step}")

    # reach (certifying)
    if a.elab:
        if not run_elab(a, roots, listed, fullname, out):
            failed.append("reach")
    elif a.static_only:
        out("[reach] not run (--static-only): the reach verdict is uncertified")
    else:
        out("[reach] FAIL: the reach verdict needs --elab (or --static-only for the static checks alone)")
        failed.append("reach")

    out(f"verdict: {'FAIL (' + ', '.join(dict.fromkeys(failed)) + ')' if failed else 'PASS'}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
