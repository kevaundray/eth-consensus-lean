#!/usr/bin/env bash
# landing-greps.sh <worktree> — the landing gates G7–G11 plus the internal-label gate, on the
# worktree's HEAD. Exit 0 iff every gate passes.
#
#   G7   (i)  elaborated: no constant reached from either root (`outage_protected_at`,
#             `meetsObligations_persists_growing`) has a `Setup` binder and uses `goldilocks`, `stock`,
#             the stock coercion or a §S constant (reach_outage.py --g7-elab, G7Check.lean; controls
#             must be `ok`, `flagged=0` for both reach modes and both roots);
#        (ii) static: no declaration of the generic Simulation directories has a `Setup` binder unless
#             it is on the §S list; no §S declaration is reachable from either root.
#   G8   no `Coe Setup BoundSetup` instance, and `goldilocks` is not reducible (no `@[reducible]`,
#        `attribute [reducible]` or `abbrev`).
#   G9   zero `TEMP(C2)`, and no `participationKind = none` Fact binder or stock instance.
#   G10  no generic declaration (over `BoundSetup`, or in the generic directories) depends on a §S one.
#   G11  no `BoundSetup` twin of a §S declaration: no other declaration with a §S entry's name whose
#        header is over `BoundSetup` (binder or file `variable`).
#   L    zero `§S`, `TEMP` and internal labels under ConsensusLean/ and docs/.
#
# Environment: SECTION_S (default lane-pa/b0-sectionS.md), SKIP_ELAB=1 skips G7(i) (needs a clean,
# built worktree; it runs `lake env lean` under /tmp/dc-lean-build.lock).
set -uo pipefail

WT="${1:?usage: landing-greps.sh <worktree>}"
WT="$(cd "$WT" && pwd)"
TOOLS="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SECTION_S="${SECTION_S:-/home/kev/work/lane-pa/b0-sectionS.md}"
GOLD=ConsensusLean/Instances/Goldilocks
GENERIC=("$GOLD/Lemmas/Simulation/" "$GOLD/Lemmas/Growing/Simulation/")
ROOTS=(outage_protected_at meetsObligations_persists_growing)
REV="$(git -C "$WT" rev-parse --short HEAD)"
TMP="$(mktemp -d /tmp/landing-greps.XXXXXX)"
trap 'rm -rf "$TMP"' EXIT
declare -A RESULT
fail=0

gate() { # gate <id> <count> <description>
  local id="$1" n="$2" what="$3"
  if [[ "$n" == 0 ]]; then RESULT[$id]="PASS"; else RESULT[$id]="FAIL ($n)"; fail=1; fi
  printf '\n### %s: %s — %s\n' "$id" "${RESULT[$id]}" "$what"
}
show() { sed 's/^/    /'; }
count() { grep -c . || true; }

echo "landing-greps on $WT @ $REV (§S list: $SECTION_S)"
cd "$WT"

# §S entries normalised for HEAD: the name reduced to its last component (G7Check resolves an entry
# by that component inside the module of its path), and the line re-resolved to that name's
# declaration in that file at HEAD (reach_outage.py matches entries by path:line only, so a stale
# line would silently drop the entry from G7(ii), G10 and G11).
python3 - "$SECTION_S" > "$TMP/sectionS.md" 2> "$TMP/sectionS.err" <<'PY'
import re, subprocess, sys
DECL = r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |public |noncomputable |nonrec )*" \
       r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+(?:[\w.']*\.)?{}(?![\w'.])"
for l in open(sys.argv[1]):
    m = re.match(r"- `([^`]+)`\s*([—-]+)\s*(\S+\.lean):(\d+)(.*)", l.rstrip("\n"))
    if not m:
        print(l, end=""); continue
    short = m.group(1).split(".")[-1]
    src = subprocess.run(["git", "show", f"HEAD:{m.group(3)}"], capture_output=True, text=True).stdout
    hits = [i + 1 for i, s in enumerate(src.splitlines()) if re.match(DECL.format(re.escape(short)), s)]
    if len(hits) != 1:
        print(f"§S entry {m.group(1)} — {m.group(3)}:{m.group(4)}: {len(hits)} declarations at HEAD",
              file=sys.stderr)
    line = hits[0] if len(hits) == 1 else int(m.group(4))
    print(f"- `{short}` {m.group(2)} {m.group(3)}:{line}{m.group(5)}")
PY

# --- G8 -------------------------------------------------------------------------------------------
git grep -nE 'instance[^:]*:[[:space:]]*Coe[[:space:]]+Setup[[:space:]]+BoundSetup|Coe[[:space:]]+Setup[[:space:]]+BoundSetup[[:space:]]*:=' \
  -- ConsensusLean ConsensusLeanTest > "$TMP/g8a" || true
git grep -nE '@\[[^]]*reducible[^]]*\][[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+goldilocks\b|attribute[[:space:]]*\[[^]]*reducible[^]]*\][[:space:]]+([A-Za-z.]*\.)?goldilocks\b|abbrev[[:space:]]+goldilocks\b' \
  -- ConsensusLean ConsensusLeanTest > "$TMP/g8b" || true
# a decorator on its own line above `def goldilocks`
git grep -nE -A1 '^@\[[^]]*reducible[^]]*\][[:space:]]*$' -- ConsensusLean ConsensusLeanTest \
  | grep -E -- '-[0-9]+-.*def[[:space:]]+goldilocks\b' >> "$TMP/g8b" || true
gate G8 "$(( $(count < "$TMP/g8a") + $(count < "$TMP/g8b") ))" \
  "no Coe Setup BoundSetup instance; goldilocks not reducible"
show < "$TMP/g8a"; show < "$TMP/g8b"

# --- G9 -------------------------------------------------------------------------------------------
git grep -nE 'TEMP\(C2\)|Fact[[:space:]]*\([^)]*participationKind[[:space:]]*=[[:space:]]*none|stock_participationKind_none|committeeSize_of_participationKind_none' \
  -- ConsensusLean ConsensusLeanTest > "$TMP/g9" || true
gate G9 "$(count < "$TMP/g9")" "zero TEMP(C2); no participationKind = none Fact binder or stock instance"
awk -F: '{print $1}' "$TMP/g9" | sort | uniq -c | sort -rn | show

# --- G7(ii), G10, §S reach: reach_outage.py (static, at HEAD) -------------------------------------
gen_args=(); for g in "${GENERIC[@]}"; do gen_args+=(--generic-dir "$g"); done
for root in "${ROOTS[@]}"; do
  python3 "$TOOLS/reach_outage.py" --repo "$WT" --rev HEAD --root "$root" --open-prefixes --static-only \
    --setup-binders --section-s "$TMP/sectionS.md" "${gen_args[@]}" > "$TMP/reach-$root.log" 2>&1 \
    || echo "reach_outage.py exited $? for $root" >> "$TMP/reach-$root.log"
done
# the dependency check does not depend on the root: read it once; an unresolved §S entry makes it
# incomplete, so it counts against G10
g10=$(grep -h '^\[deps\] generic → §S violations:' "$TMP/reach-${ROOTS[0]}.log" | awk '{s+=$NF} END{print s+0}')
g10=$(( g10 + $(count < "$TMP/sectionS.err") ))
grep -q '^\[deps\]' "$TMP/reach-${ROOTS[0]}.log" || g10="no-output"
gate G10 "$g10" "no generic declaration depends on a §S declaration (every §S entry resolved at HEAD)"
sed -n '/^\[deps\]/,/^\[by-name\] §S/p' "$TMP/reach-${ROOTS[0]}.log" | grep -v '^\[by-name\] §S' | show
grep -h '^§S entries not at a declaration line' "$TMP"/reach-*.log | sort -u | show
show < "$TMP/sectionS.err"

awk '/§S declarations reachable from root:/ {on=1; next} /^[^ ]/ {on=0} on && /^    / {print}' \
  "$TMP"/reach-*.log | sort -u > "$TMP/sreach"
sreach=$(count < "$TMP/sreach")
# G7(ii) static: Setup binders in the generic directories, outside §S
python3 - "$WT" "$TMP/sectionS.md" "${GENERIC[@]}" > "$TMP/g7ii" <<'PY'
import re, subprocess, sys
wt, sec, gens = sys.argv[1], sys.argv[2], sys.argv[3:]
ent = set()
for l in open(sec):
    m = re.search(r"`([^`]+)`\s*[—-]+\s*(\S+\.lean):\d+", l)
    if m: ent.add((m.group(2), m.group(1)))
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |public |noncomputable |nonrec )*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)", re.M)
files = subprocess.run(["git", "-C", wt, "ls-files", "--", *gens], capture_output=True, text=True).stdout.split()
for f in files:
    if not f.endswith(".lean"): continue
    t = open(f"{wt}/{f}").read()
    t = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), t, flags=re.S)
    var = any(re.search(r"[({]\s*S\s*:\s*Setup\s*[)}]", b)
              for b in re.findall(r"^variable\b[^\n]*(?:\n[ \t]+[^\n]*)*", t, re.M))
    ms = list(DECL.finditer(t))
    for i, m in enumerate(ms):
        body = t[m.start(): ms[i + 1].start() if i + 1 < len(ms) else len(t)]
        head = body.split(":=", 1)[0]
        name = m.group(1).split(".")[-1]
        sb = re.search(r"[({]\s*[^(){}:]*:\s*Setup\s*[)}]", head) or (
            var and re.search(r"(?<![\w.'])S(?![\w'])", head))
        if sb and (f, name) not in ent:
            print(f"{f}:{t[:m.start()].count(chr(10)) + 1}: {m.group(1)}")
PY
gate G7ii "$(( $(count < "$TMP/g7ii") + sreach ))" \
  "no Setup binder in the generic directories outside §S; no §S declaration reachable from a root"
show < "$TMP/g7ii"
sed 's/^/§S reachable: /' "$TMP/sreach" | show

# --- G11 ------------------------------------------------------------------------------------------
python3 - "$WT" "$TMP/sectionS.md" > "$TMP/g11" <<'PY'
import re, subprocess, sys
wt, sec = sys.argv[1], sys.argv[2]
ent = {}
for l in open(sec):
    m = re.search(r"`([^`]+)`\s*[—-]+\s*(\S+\.lean):(\d+)", l)
    if m: ent.setdefault(m.group(1), set()).add(m.group(2))
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |public |noncomputable |nonrec )*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)", re.M)
files = subprocess.run(["git", "-C", wt, "ls-files", "--", "ConsensusLean"], capture_output=True,
                       text=True).stdout.split()
for f in files:
    if not f.endswith(".lean"): continue
    t = open(f"{wt}/{f}").read()
    t = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), t, flags=re.S)
    var = any(re.search(r"[({]\s*S\s*:\s*BoundSetup\s*[)}]", b)
              for b in re.findall(r"^variable\b[^\n]*(?:\n[ \t]+[^\n]*)*", t, re.M))
    ms = list(DECL.finditer(t))
    for i, m in enumerate(ms):
        name = m.group(1).split(".")[-1]
        if name not in ent or f in ent[name]: continue
        body = t[m.start(): ms[i + 1].start() if i + 1 < len(ms) else len(t)]
        head = body.split(":=", 1)[0]
        if re.search(r"\bBoundSetup\b", head) or (var and re.search(r"(?<![\w.'])S(?![\w'])", head)):
            print(f"{f}:{t[:m.start()].count(chr(10)) + 1}: {m.group(1)} (twin of §S `{name}`)")
PY
gate G11 "$(count < "$TMP/g11")" "no BoundSetup twin of a §S declaration"
show < "$TMP/g11"

# --- G7(i): elaborated check ------------------------------------------------------------------------
if [[ "${SKIP_ELAB:-0}" == 1 ]]; then
  RESULT[G7i]="SKIPPED"; printf '\n### G7i: SKIPPED (SKIP_ELAB=1)\n'
else
  g7=0; : > "$TMP/g7i"
  for root in "${ROOTS[@]}"; do
    for mode in by-name +dots; do
      python3 "$TOOLS/reach_outage.py" --repo "$WT" --rev HEAD --root "$root" --open-prefixes \
        --section-s "$TMP/sectionS.md" --g7-elab "$WT" --g7-mode "$mode" > "$TMP/g7-$root-$mode.log" 2>&1
      rc=$?
      out="$TMP/g7-$root-$mode.log"
      flagged=$(grep -E '^== .*: reached=' "$out" | grep -oE 'flagged=[0-9]+' | cut -d= -f2 | awk '{s+=$1} END{if (NR) print s}')
      ctrl_bad=$(grep -c 'CONTROL FAILED' "$out" || true)
      echo "$root [$mode]: exit=$rc flagged=${flagged:-none} control-failures=$ctrl_bad" >> "$TMP/g7i"
      if [[ $rc != 0 || -z "$flagged" ]]; then g7=$((g7 + 1)); grep -E 'error|Error|§S:' "$out" | head -5 | sed 's/^/      /' >> "$TMP/g7i"
      else g7=$((g7 + flagged + ctrl_bad)); grep -E '^    FLAG ' "$out" | sed 's/^/  /' >> "$TMP/g7i"; fi
    done
  done
  gate G7i "$g7" "elaborated: no reached Setup-bound constant uses goldilocks/stock/coercion/§S (both roots, both modes)"
  show < "$TMP/g7i"
fi

# --- L: §S, TEMP and internal labels under ConsensusLean/ and docs/ ------------------------------------
LABELS='§S(?![a-z])|\bTEMP\b|scope-\(ii\)|\bB[0-4]\.([0-9]|[a-z])\b|\*\*B[0-4]\b|\(F3′?\)|\b(at|until|after|before|by|in|removed at) (D[12]|C[1-4][a-c]?|G[0-9]+)\b(?![.′\d])|\bgate G[0-9]+\b|\b9124(d968)?\b|\bC[1-4][a-c]\b|\bC2-records\b|records\(2\)|\b(cp[0-9]+(prime)?|round[0-9]+|GO Engine|TrustedCtr|T-ctr|PROVISIONAL|BOX|Opus|Astra|Fable|fradamt)\b'
git grep -nP "$LABELS" -- ConsensusLean docs > "$TMP/labels" || true
gate L "$(count < "$TMP/labels")" "zero §S / TEMP / internal labels under ConsensusLean/ and docs/"
echo "    by label:"
git grep -ohP "$LABELS" -- ConsensusLean docs | sort | uniq -c | sort -rn | sed 's/^/      /'
echo "    by file:"
awk -F: '{print $1}' "$TMP/labels" | sort | uniq -c | sort -rn | sed 's/^/      /'
# Sites whose exact line is already in the base the port starts from (BASE, default 9124d968).
BASE="${BASE:-9124d968}"
echo "    sites whose line is unchanged from $BASE:"
while IFS= read -r hit; do
  f="${hit%%:*}"; rest="${hit#*:}"; text="${rest#*:}"
  git show "$BASE:$f" 2>/dev/null | grep -qxF -- "$text" && echo "      $f:${rest%%:*}: ${text:0:140}"
done < "$TMP/labels"

# --- summary --------------------------------------------------------------------------------------
printf '\n== summary @ %s\n' "$REV"
for g in G7i G7ii G8 G9 G10 G11 L; do printf '  %-5s %s\n' "$g" "${RESULT[$g]:-not run}"; done
exit "$fail"
