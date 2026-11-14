#!/usr/bin/env python3
"""Compare two instance-spec snapshots by constant: print added/removed constants and a table of
every constant whose type hash or value hash changed.  usage: hash-table.py OLD NEW"""
import re, sys

HASH = re.compile(r"#(-|\d+)/(-|\d+)$")

def parse(path):
    out, cur = {}, None
    for line in open(path, encoding="utf-8"):
        line = line.rstrip("\n")
        if not line or line.startswith("#") or line.split(" ", 1)[0] in ("toolchain", "package"):
            continue
        if not line.startswith(" "):
            kind, name = line.split(" ", 2)[:2]
            cur = (kind, name)
            m = HASH.search(line)
            if m and line.endswith(m.group(0)) and " : " not in line:
                out[name] = (kind, m.group(1), m.group(2), line)
                cur = None
            else:
                out[name] = (kind, None, None, line)
            continue
        m = HASH.search(line.strip())
        if cur and m:
            kind, name = cur
            out[name] = (kind, m.group(1), m.group(2), out[name][3])
            cur = None
    return out

old, new = parse(sys.argv[1]), parse(sys.argv[2])
removed = sorted(set(old) - set(new))
added = sorted(set(new) - set(old))
print(f"constants: old {len(old)}  new {len(new)}")
print("removed:", *removed or ["(none)"], sep="\n  ")
print("added:", *added or ["(none)"], sep="\n  ")
changed = [n for n in sorted(set(old) & set(new)) if old[n][1:3] != new[n][1:3]]
print(f"\nhash changes: {len(changed)}")
print("| constant | old type hash | new type hash | old value hash | new value hash |")
print("|---|---|---|---|---|")
for n in changed:
    o, w = old[n], new[n]
    print(f"| `{n}` | {o[1]} | {w[1]} | {o[2]} | {w[2]} |")
print(f"\ntype-hash changes: {sum(old[n][1] != new[n][1] for n in changed)}")
print(f"header-line (displayed signature) changes: {sum(old[n][3] != new[n][3] for n in changed)}")
