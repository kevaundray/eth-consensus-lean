import ConsensusLean
import Solution
/-!
# G7(i), refined (c56-2325): elaborated-constant check

Not part of the repository. Run from the worktree, with the built `.lake`:

    G7_NAMES=reach.txt G7_SECTION_S=/home/kev/work/lane-pa/b0-sectionS.md \
      flock /tmp/dc-lean-build.lock env LEAN_NUM_THREADS=2 \
      lake env lean /home/kev/work/lane-cov/tools/G7Check.lean

* `G7_NAMES`: `reach_outage.py --dump` output (`mode<TAB>full name<TAB>file:line`); several files may
  be given, separated by `,`; each is reported separately.
* `G7_MODE`: which closure of the dump to check (default `by-name`).
* `G7_SECTION_S`: the §S list (`- \`name\` — path.lean:line`); each entry is resolved to the
  unique constant with that last component in the module named by the path.

A reached constant is flagged when (1) its type's ∀-telescope has a binder of type `Setup`
(section variables are ∀-binders of the elaborated type) and (2) its elaborated type or value
(proofs included; for an inductive, its constructors' types) uses `goldilocks`, `stock`,
`stockBoundSetupCoe` or a §S constant. Auxiliary constants the declaration's elaboration produced
under its own name (`c.proof_n`, `c.match_n`, `where` helpers) count as part of `c`. Exempt by
name: `goldilocks`, `PubState`.

Controls (always checked): `G7Ctrl.g7_ctrl` (a `(S : Setup)` statement applying a generic
`(S : BoundSetup)` lemma at `⟨S, stock⟩`) must be flagged; `G7Ctrl.g7_neg` (the same lemma
over `(S : BoundSetup)`) and `G7Ctrl.g7_neg_setup` (a `(S : Setup)` declaration reading only a
`Setup` field) must not.

Fail-closed: an empty §S list, a control mismatch, an unresolved or flagged reached constant, or a
reached axiom other than `propext`, `Classical.choice` and `Quot.sound` is an error (nonzero exit).
-/

set_option autoImplicit false

namespace G7Ctrl
open Consensus Consensus.Shape Consensus.Goldilocks Consensus.Goldilocks.AsChainShape
open Consensus.Goldilocks.Simulation

/-- Positive control: `S : Setup` reaches the generic lemma at the stock binding `⟨S, stock⟩`. -/
theorem g7_ctrl {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocksWith ⟨S, stock⟩)) E) (y : Fin (Fintype.card V)) :
    y ∈ honestKeys ⟨S, stock⟩ rho ↔ rho.key y ∉ rho.faultyAt 0 :=
  mem_honestKeys_iff ⟨S, stock⟩ rho y

/-- Negative control: the same lemma, generic. -/
theorem g7_neg {V : Type} [Fintype V] {E : Env V} (S : BoundSetup)
    (rho : Model.Run (compiled (goldilocksWith S)) E) (y : Fin (Fintype.card V)) :
    y ∈ honestKeys S rho ↔ rho.key y ∉ rho.faultyAt 0 :=
  mem_honestKeys_iff S rho y

/-- Negative control: a `Setup` binder reading only a field. -/
theorem g7_neg_setup (S : Setup) : S.k ≤ S.k + 1 := Nat.le_succ _

end G7Ctrl

open Lean

namespace G7

def setupN : Name := ``Consensus.Goldilocks.AsChainShape.Setup
def stockFamily : Array Name :=
  #[``Consensus.Goldilocks.AsChainShape.goldilocks, ``Consensus.Goldilocks.AsChainShape.stock,
    `Consensus.Goldilocks.stockBoundSetupCoe]
def exempt : Array Name :=
  #[``Consensus.Goldilocks.AsChainShape.goldilocks, ``Consensus.Goldilocks.AsChainShape.PubState]
def controls : Array (Name × Bool) :=
  #[(``G7Ctrl.g7_ctrl, true), (``G7Ctrl.g7_neg, false), (``G7Ctrl.g7_neg_setup, false)]

/-- A binder of type `Setup` in the ∀-telescope. -/
partial def setupBinder : Expr → Bool
  | .forallE _ d b _ => d.cleanupAnnotations.isConstOf setupN || setupBinder b
  | .mdata _ e => setupBinder e
  | _ => false

/-- The expressions elaborated for `ci`: its type, its value, and its constructors' types. -/
def exprsOf (env : Environment) (ci : ConstantInfo) : Array Expr :=
  let ctors := match ci with
    | .inductInfo v => v.ctors.toArray.filterMap fun c => (env.find? c).map (·.type)
    | _ => #[]
  let val := match ci with
    | .defnInfo v => #[v.value]
    | .thmInfo v => #[v.value]
    | .opaqueInfo v => #[v.value]
    | _ => #[]
  #[ci.type] ++ val ++ ctors

/-- Constants used by `c`'s elaboration, following `c`'s own auxiliary constants. Returns the
used constants and whether `c` had a value to inspect. -/
partial def usedBy (env : Environment) (c : Name) : NameSet × Bool := Id.run do
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  let mut todo := #[c]
  let mut hasVal := false
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if n == c then
      hasVal := match ci with
        | .defnInfo _ | .thmInfo _ | .opaqueInfo _ | .inductInfo _ => true
        | _ => false
    for e in exprsOf env ci do
      for u in e.getUsedConstants do
        out := out.insert u
        if u != c && c.isPrefixOf u && !seen.contains u then todo := todo.push u
  return (out, hasVal)

def lines (path : String) : IO (Array String) := do
  return ((← IO.FS.readFile path).splitOn "\n").toArray.filter (·.any (!·.isWhitespace))

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `«this file»

/-- §S entries `- \`name\` — path.lean:line`, resolved within the module named by the path. -/
def sectionS (env : Environment) (path : String) : IO (Array Name) := do
  let mut out := #[]
  for l in ← lines path do
    let parts := l.splitOn "`"
    unless l.startsWith "- `" && parts.length ≥ 3 do continue
    let short := parts[1]!
    let rest := (parts[2]!.splitOn ".lean:")
    unless rest.length ≥ 2 do continue
    let file := ((rest[0]!.splitOn " ").getLast!)
    let mod := (file.replace "/" ".").toName
    let some idx := env.getModuleIdx? mod
      | throw <| IO.userError s!"§S: module {mod} not in the environment"
    let cands := env.header.moduleData[idx.toNat]!.constNames.filter fun n =>
      (privateToUserName? n |>.getD n).getString! == short
    unless cands.size == 1 do
      throw <| IO.userError s!"§S: {short} in {mod}: {cands.size} candidates {cands}"
    out := out.push cands[0]!
  if out.isEmpty then throw <| IO.userError "§S list is empty"
  return out

def resolve (env : Environment) (priv : Std.HashMap Name Name) (s : String) : Option Name :=
  let n := s.toName
  -- `_root_.X` declared inside a namespace is `X` (the dump may carry it as `NS.X`)
  let cs := n.components
  let cands := n :: ((List.range cs.length).filter (fun i => i > 0 && cs[i]! == `Consensus ||
      i > 0 && cs[i - 1]! == `_root_)).map (Name.fromComponents <| cs.drop ·)
  cands.findSome? fun n => if env.contains n then some n else priv.get? n

def run : CoreM Unit := do
  let env ← getEnv
  let mode := (← IO.getEnv "G7_MODE").getD "by-name"
  let some names := ← IO.getEnv "G7_NAMES" | throwError "G7_NAMES unset"
  let some secPath := ← IO.getEnv "G7_SECTION_S" | throwError "G7_SECTION_S unset"
  let sec ← sectionS env secPath
  IO.println s!"§S constants: {sec.size}"
  for n in sec do IO.println s!"    {n}"
  let bad : NameSet := (stockFamily ++ sec).foldl (·.insert ·) {}
  -- private constants of the project, by user name
  let mut priv : Std.HashMap Name Name := {}
  for i in [:env.header.moduleNames.size] do
    if (`ConsensusLean).isPrefixOf env.header.moduleNames[i]! then
      for n in env.header.moduleData[i]!.constNames do
        if let some u := privateToUserName? n then priv := priv.insert u n
  -- returns (setup binder, offenders, has value)
  let check (n : Name) : Option (Bool × Array Name × Bool) := do
    let ci ← env.find? n
    let (used, hasVal) := usedBy env n
    let off := used.toArray.filter (bad.contains ·) |>.qsort Name.lt
    return (setupBinder ci.type, off, hasVal)
  IO.println "controls:"
  let mut failed := false
  for (n, expect) in controls do
    let some (sb, off, _) := check n | throwError "control {n} missing"
    let flagged := sb && !off.isEmpty
    if flagged != expect then failed := true
    IO.println s!"    {n}: setupBinder={sb} offenders={off} → {if flagged then "FLAGGED" else "pass"} \
      ({if flagged == expect then "ok" else "CONTROL FAILED"})"
  for file in names.splitOn "," do
    let rows := (← lines file).filterMap fun l =>
      match l.splitOn "\t" with
      | [m, nm, loc] => if m == mode then some (nm, loc) else none
      | _ => none
    let mut unresolved := #[]
    let mut sb := #[]
    let mut flagged := #[]
    let mut axioms := #[]
    for (nm, loc) in rows do
      let some n := resolve env priv nm | unresolved := unresolved.push s!"{nm} @ {loc}"; continue
      if let some (.axiomInfo _) := env.find? n then
        unless #[`propext, `Classical.choice, `Quot.sound].contains n do
          axioms := axioms.push n
      let some (isSB, off, hasVal) := check n | continue
      unless isSB do continue
      let tag := if exempt.contains n then "exempt" else if off.isEmpty then "pass" else "FLAG"
      sb := sb.push s!"    {tag} {n} [{moduleOf env n}]{if hasVal then "" else " (no value)"} \
        {if off.isEmpty then "" else s!"← {off}"}"
      if tag == "FLAG" then flagged := flagged.push n
    IO.println s!"== {file} [{mode}]: reached={rows.size} unresolved={unresolved.size} \
      bodiless(axiom)={axioms.size} setupBinder={sb.size} flagged={flagged.size}"
    for n in axioms do IO.println s!"    axiom {n}"
    for u in unresolved do IO.println s!"    unresolved {u}"
    for l in sb do IO.println l
    if !unresolved.isEmpty || !flagged.isEmpty || !axioms.isEmpty then failed := true
  if failed then throwError "G7 failed: control mismatch, unresolved constant or forbidden edge"

end G7

#eval G7.run
