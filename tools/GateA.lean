import ConsensusLean
/-!
# Gate (a) on the elaborated closure of the two outage roots (records(2) plan, §E)

Run from a clean, built worktree:

    GATEA_SECTION_S=/home/kev/work/lane-pa/b0-sectionS.md \
      flock /tmp/dc-lean-build.lock env LEAN_NUM_THREADS=2 lake env lean GateA.lean

Closure as in `ElabReach.lean` (type + value, constructors, recursor rules, `Expr.const` and
`Expr.proj` structure names; project constants only). Checks, each must print 0:
* `size-premise`: binders of a root's type whose type is `_ .committeeSize = _ .n` (any `Eq` whose
  left side is a `committeeSize` application), or a `Fact` binder mentioning `participationKind`;
* `run-record-stock`: reached constants mentioning a run-record `stock` projection (by constant or
  primitive projection) of `GoldilocksRun`, `Growing.GoldilocksRun`, `SA.ACRun`, `SA.ACRunU`,
  `SA.ACRunUS`, `SA.Growing.ACRun` (vacuous once the fields are deleted; listed so the check does not
  silently pass while they exist);
* `mayVote-stock`: reached `trace_mayVote_stock`, `mayVote_stock`, `mayVote_stock_at`;
* `hmv`: reached `*.OutageLockPremises.hmv`, and reached constants whose type binds a variable named
  `hmv`;
* `fact-pk`: reached constants whose type has `Fact` and `participationKind`, and reached
  `stock_participationKind_none` / `committeeSize_of_participationKind_none`;
* `sectionS`: reached constants of the §S list (`- \`name\` — path.lean:line`, resolved as in
  `G7Check.lean`).
-/
set_option autoImplicit false
open Lean Meta

namespace GateA

def roots : Array Name :=
  #[`Consensus.Goldilocks.Obligations.Growing.outage_protected_at,
    `Consensus.Goldilocks.Obligations.Growing.meetsObligations_persists_growing]

def records : Array Name :=
  #[`Consensus.Goldilocks.GoldilocksRun, `Consensus.Goldilocks.Growing.GoldilocksRun,
    `Consensus.Goldilocks.SA.ACRun, `Consensus.Goldilocks.SA.ACRunU,
    `Consensus.Goldilocks.SA.ACRunUS, `Consensus.Goldilocks.SA.Growing.ACRun]

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

def isProject (env : Environment) (n : Name) : Bool :=
  (`ConsensusLean).isPrefixOf (moduleOf env n) || (`ConsensusLeanTest).isPrefixOf (moduleOf env n)

def userName (n : Name) : Name := (privateToUserName? n).getD n

partial def collect (e : Expr) : NameSet × Std.HashSet (Name × Nat) := Id.run do
  let mut cs : NameSet := {}
  let mut ps : Std.HashSet (Name × Nat) := {}
  let mut seen : Std.HashSet Expr := {}
  let mut todo := #[e]
  while h : todo.size > 0 do
    let x := todo.back
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .const n _ => cs := cs.insert n
    | .app f a => todo := todo.push f |>.push a
    | .lam _ d b _ | .forallE _ d b _ => todo := todo.push d |>.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | .mdata _ b => todo := todo.push b
    | .proj s i b => ps := ps.insert (s, i); cs := cs.insert s; todo := todo.push b
    | _ => pure ()
  return (cs, ps)

def exprsOf (env : Environment) (ci : ConstantInfo) : Array Expr × Array Name :=
  match ci with
  | .defnInfo v => (#[v.type, v.value], #[])
  | .thmInfo v => (#[v.type, v.value], #[])
  | .opaqueInfo v => (#[v.type, v.value], #[])
  | .inductInfo v => (#[v.type] ++ v.ctors.toArray.filterMap fun c => (env.find? c).map (·.type), #[])
  | .ctorInfo v => (#[v.type], #[v.induct])
  | .recInfo v => (#[v.type] ++ v.rules.toArray.map (·.rhs), #[])
  | ci => (#[ci.type], #[])

def closure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut frontier := #[root]
  while !frontier.isEmpty do
    let mut next := #[]
    for n in frontier do
      let some ci := env.find? n | continue
      let (es, extra) := exprsOf env ci
      let mut s : NameSet := extra.foldl (·.insert ·) {}
      for e in es do s := (collect e).1.foldl (·.insert ·) s
      for u in s do
        if isProject env u && !seen.contains u then
          seen := seen.insert u
          next := next.push u
    frontier := next
  return seen

def projKey (env : Environment) (t : Name) : Option (Name × Nat) := do
  let info ← env.getProjectionFnInfo? t
  let some (.ctorInfo c) := env.find? info.ctorName | none
  return (c.induct, info.i)

def isSizeEq (d : Expr) : Bool :=
  d.isAppOfArity ``Eq 3 && (match d.appFn!.appArg!.getAppFn with
    | .const n _ => n.isStr && n.getString! == "committeeSize"
    | _ => false)

def lastIs (n : Name) (s : String) : Bool := (userName n).isStr && (userName n).getString! == s

def sectionS (env : Environment) (path : String) : IO (Array Name) := do
  let mut out := #[]
  for l in (← IO.FS.readFile path).splitOn "\n" do
    let parts := l.splitOn "`"
    unless l.startsWith "- `" && parts.length ≥ 3 do continue
    let short := parts[1]!
    let rest := parts[2]!.splitOn ".lean:"
    unless rest.length ≥ 2 do continue
    let file := (rest[0]!.splitOn " ").getLast!
    let mod := (file.replace "/" ".").toName
    let some idx := env.getModuleIdx? mod
      | throw <| IO.userError s!"§S: module {mod} not in the environment"
    let cands := env.header.moduleData[idx.toNat]!.constNames.filter fun n =>
      (userName n).getString! == (short.splitOn ".").getLast!
    unless cands.size == 1 do
      throw <| IO.userError s!"§S: {short} in {mod}: {cands.size} candidates {cands}"
    out := out.push cands[0]!
  return out

def run : MetaM Unit := do
  let env ← getEnv
  let some secPath ← IO.getEnv "GATEA_SECTION_S" | throwError "GATEA_SECTION_S unset"
  let sec ← sectionS env secPath
  IO.println s!"§S constants resolved: {sec.size}"
  let pk := env.constants.fold (init := #[]) fun acc n _ =>
    if isProject env n && (userName n).toString.endsWith "VoteBinding.participationKind" then acc.push n
    else acc
  let stockProj := records.filterMap fun R => if env.contains (R ++ `stock) then some (R ++ `stock) else none
  let stockKeys := stockProj.filterMap (projKey env)
  IO.println s!"run-record stock fields present: {stockProj}"
  let mut total := 0
  for r in roots do
    let c := closure env r
    let some rci := env.find? r | throwError "root {r} missing"
    -- size premises / Fact binders on the root's type
    let mut prem := #[]
    let mut t := rci.type
    for _ in [:500] do
      match t with
      | .forallE nm d b _ =>
        let d' := d.consumeMData
        let (dc, _) := collect d'
        if isSizeEq d' || (dc.contains ``Fact && pk.any dc.contains) then prem := prem.push nm
        t := b
      | .mdata _ b => t := b
      | _ => break
    let mut hits : Array (String × Name) := #[]
    for n in c do
      let some ci := env.find? n | continue
      let (es, _) := exprsOf env ci
      let mut cs : NameSet := {}
      let mut ps : Std.HashSet (Name × Nat) := {}
      for e in es do
        let (a, b) := collect e
        cs := a.foldl (·.insert ·) cs
        ps := b.fold (·.insert ·) ps
      if stockProj.any cs.contains || stockKeys.any ps.contains then hits := hits.push ("run-record-stock", n)
      if lastIs n "trace_mayVote_stock" || lastIs n "mayVote_stock" || lastIs n "mayVote_stock_at" then
        hits := hits.push ("mayVote-stock", n)
      if (userName n).toString.endsWith "OutageLockPremises.hmv" then hits := hits.push ("hmv", n)
      let mut ty := ci.type
      for _ in [:500] do
        match ty with
        | .forallE nm d b _ =>
          -- the TEMP shape `∀ y s, (ini y).mayVote s = true`: quantified over a node `Fin _` first
          -- (per-node permission hypotheses `∀ i, (tr.state y i).ac.mayVote s` are not TEMP)
          if nm == `hmv then
            match d.consumeMData with
            | .forallE _ d₀ _ _ => if d₀.consumeMData.isAppOf ``Fin then hits := hits.push ("hmv", n)
            | _ => pure ()
          ty := b
        | .mdata _ b => ty := b
        | _ => break
      let (tc, _) := collect ci.type
      if tc.contains ``Fact && pk.any tc.contains then hits := hits.push ("fact-pk", n)
      if lastIs n "stock_participationKind_none" || lastIs n "committeeSize_of_participationKind_none" then
        hits := hits.push ("fact-pk", n)
      if sec.contains n then hits := hits.push ("sectionS", n)
    IO.println s!"\n== {r}: {c.size} constants; size-premise binders {prem.size} {prem}"
    for k in ["run-record-stock", "mayVote-stock", "hmv", "fact-pk", "sectionS"] do
      let hs := hits.filter (·.1 == k)
      IO.println s!"  {k}: {hs.size}"
      for (_, n) in hs.toList.take 40 do IO.println s!"    {n} [{moduleOf env n}]"
    total := total + prem.size + hits.size
  IO.println s!"\nGATE (a): {if total == 0 then "PASS" else s!"FAIL ({total})"}"

end GateA

#eval GateA.run
