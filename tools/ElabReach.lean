import ConsensusLean
import ConsensusLeanTest.Goldilocks.Regimes.ProposerHoldRun.Cast
/-!
# Elaborated constant closure of the gate-(a) roots (c56-0501)

Not part of the repository. Run from the worktree, with the built `.lake`:

    flock /tmp/dc-lean-build.lock env LEAN_NUM_THREADS=2 \
      lake env lean /home/kev/work/lane-cov/tools/ElabReach.lean

Closure, per root, separately: breadth-first over the *elaborated* environment. The edges of a
constant `c` are every constant occurring in
* its type,
* its value (`def`/`theorem`/`opaque`: proofs included, read from the loaded `.olean` data),
* for an inductive: its constructors' types; for a constructor: its inductive; for a recursor:
  its rule right-hand sides,
counting both `Expr.const` and the structure name of every primitive projection `Expr.proj`.
Only constants defined in a `ConsensusLean*` module are expanded or kept (Lean core, Std, Batteries,
Mathlib are excluded: they are not project modules and cannot import the project, so nothing
project-side is reachable through them). Auxiliary constants (`c.match_n`, `c.proof_n`,
`c.eq_n`, `where` helpers, private names) are ordinary nodes: they are entered exactly when an
elaborated term references them. A source line is "in the closure" when the declaration whose
range contains it is reached; a reached auxiliary `c.*` of an unreached `c` is reported separately.
BFS gives shortest paths.
-/

set_option autoImplicit false

open Lean Meta

namespace ElabReach

def roots : Array Name :=
  #[`Consensus.Goldilocks.Obligations.Growing.outage_protected_at,
    `Consensus.Goldilocks.Obligations.Growing.meetsObligations_persists_growing]

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

def isProject (env : Environment) (n : Name) : Bool :=
  (`ConsensusLean).isPrefixOf (moduleOf env n) || (`ConsensusLeanTest).isPrefixOf (moduleOf env n)

def userName (n : Name) : Name := (privateToUserName? n).getD n

/-- Constants and projected structure names occurring in `e`. -/
partial def refs (e : Expr) : NameSet := Id.run do
  let mut out : NameSet := {}
  let mut seen : Std.HashSet Expr := {}
  let mut todo := #[e]
  while h : todo.size > 0 do
    let x := todo.back
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .const n _ => out := out.insert n
    | .app f a => todo := todo.push f |>.push a
    | .lam _ d b _ | .forallE _ d b _ => todo := todo.push d |>.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | .mdata _ b => todo := todo.push b
    | .proj s _ b => out := out.insert s; todo := todo.push b
    | _ => pure ()
  return out

def exprsOf (env : Environment) (ci : ConstantInfo) : Array Expr × Array Name :=
  match ci with
  | .defnInfo v => (#[v.type, v.value], #[])
  | .thmInfo v => (#[v.type, v.value], #[])
  | .opaqueInfo v => (#[v.type, v.value], #[])
  | .inductInfo v => (#[v.type] ++ v.ctors.toArray.filterMap fun c => (env.find? c).map (·.type), #[])
  | .ctorInfo v => (#[v.type], #[v.induct])
  | .recInfo v => (#[v.type] ++ v.rules.toArray.map (·.rhs), #[])
  | ci => (#[ci.type], #[])

def edges (env : Environment) (n : Name) : Array Name := Id.run do
  let some ci := env.find? n | return #[]
  let (es, extra) := exprsOf env ci
  let mut s : NameSet := extra.foldl (·.insert ·) {}
  for e in es do s := (refs e).foldl (·.insert ·) s
  return s.toArray.filter (isProject env ·) |>.qsort Name.lt

/-- BFS closure with parent pointers. -/
def closure (env : Environment) (root : Name) : Std.HashMap Name Name := Id.run do
  let mut parent : Std.HashMap Name Name := ({} : Std.HashMap Name Name).insert root root
  let mut frontier := #[root]
  while !frontier.isEmpty do
    let mut next := #[]
    for n in frontier do
      for u in edges env n do
        unless parent.contains u do
          parent := parent.insert u n
          next := next.push u
    frontier := next
  return parent

def pathTo (parent : Std.HashMap Name Name) (n : Name) : List Name := Id.run do
  let mut out := [n]
  let mut cur := n
  for _ in [:100000] do
    let p := parent.getD cur cur
    if p == cur then break
    out := p :: out
    cur := p
  return out

def fmtPath (env : Environment) (p : List Name) : String :=
  " →\n        ".intercalate (p.map fun n => s!"{userName n} [{moduleOf env n}]")

def fileOf (m : Name) : String := "/".intercalate (m.components.map (·.toString)) ++ ".lean"

def resolveSuffix (env : Environment) (suffix : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if isProject env n && suffix.isSuffixOf (userName n) then acc.push n else acc

/-- The declaration (with a declaration range) of module `m` whose range contains `line`
(innermost), plus its range. -/
def enclosing (m : Name) (line : Nat) : CoreM (Option (Name × Nat × Nat)) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? m | throwError "module {m} not loaded"
  let mut best : Option (Name × Nat × Nat) := none
  for n in env.header.moduleData[idx.toNat]!.constNames do
    let some r ← findDeclarationRanges? n | continue
    let a := r.range.pos.line
    let b := r.range.endPos.line
    unless a ≤ line && line ≤ b do continue
    best := match best with
      | some (_, a', b') => if b - a < b' - a' then some (n, a, b) else best
      | none => some (n, a, b)
  return best

def sourceLine (m : Name) (line : Nat) : IO String := do
  let ls := (← IO.FS.readFile (fileOf m)).splitOn "\n"
  return (ls.getD (line - 1) "").trimAscii.toString

/-- Owning declaration of `n` (the nearest of `n` and its prefixes with a source range). -/
def owner (n : Name) : CoreM (Name × Nat × Nat) := do
  let mut cur := n
  for _ in [:64] do
    if cur.isAnonymous then break
    if let some r ← findDeclarationRanges? cur then
      return (cur, r.range.pos.line, r.range.endPos.line)
    cur := cur.getPrefix
  return (n, 0, 0)

/-- The primitive-projection key `(structure, field index)` of a projection function. -/
def projKey (env : Environment) (t : Name) : Option (Name × Nat) := do
  let info ← env.getProjectionFnInfo? t
  let some (.ctorInfo c) := env.find? info.ctorName | none
  return (c.induct, info.i)

/-- Whether `e` mentions `t` (as a constant or as its primitive projection), memoised. -/
partial def mentions (t : Name) (pk : Option (Name × Nat)) (memo : IO.Ref (Std.HashMap Expr Bool))
    (e : Expr) : IO Bool := do
  if let some b := (← memo.get)[e]? then return b
  let b ← match e with
    | .const n _ => pure (n == t)
    | .app f a => do if ← mentions t pk memo f then pure true else mentions t pk memo a
    | .lam _ d b _ | .forallE _ d b _ => do
      if ← mentions t pk memo d then pure true else mentions t pk memo b
    | .letE _ ty v b _ => do
      if ← mentions t pk memo ty then pure true
      else if ← mentions t pk memo v then pure true else mentions t pk memo b
    | .mdata _ b => mentions t pk memo b
    | .proj s i b => do if pk == some (s, i) then pure true else mentions t pk memo b
    | _ => pure false
  memo.modify (·.insert e b)
  return b

def clip (s : String) : String := if s.length > 500 then toString (s.take 500) ++ " …" else s

/-- Each occurrence of `t` in `e`, labelled with the innermost structure-constructor field whose
argument contains it (`outside any record field` otherwise) and that argument, pretty-printed. -/
partial def occ (t : Name) (pk : Option (Name × Nat)) (memo : IO.Ref (Std.HashMap Expr Bool))
    (e : Expr) (ctx : String) : MetaM (Array String) := do
  unless ← mentions t pk memo e do return #[]
  let env ← getEnv
  match e with
  | .const .. => return #[ctx]
  | .proj s i b =>
    let here := if pk == some (s, i) then #[ctx] else #[]
    return here ++ (← occ t pk memo b ctx)
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let ctorCtx : Option (Name × Array Name × Nat) := match fn with
      | .const c _ => match env.find? c with
        | some (.ctorInfo v) =>
          if isStructure env v.induct then some (c, getStructureFields env v.induct, v.numParams)
          else none
        | _ => none
      | _ => none
    let mut out := if fn.isConstOf t then #[ctx] else #[]
    unless fn.isConst do out := out ++ (← occ t pk memo fn ctx)
    for h : i in [:args.size] do
      let a := args[i]
      let ctx' ← match ctorCtx with
        | some (c, fs, np) =>
          if i ≥ np then
            let a' := a.consumeMData
            let shape :=
              if a'.getAppFn.isConstOf t then "the projection itself, applied: "
              else match a' with
                | .proj s j _ => if pk == some (s, j) then "the primitive projection itself: " else "other term: "
                | _ => "other term: "
            pure s!"field `{fs[i - np]?.getD .anonymous}` of `{c}` := {shape}{clip (toString a)}"
          else pure ctx
        | none => pure ctx
      out := out ++ (← occ t pk memo a ctx')
    return out
  | .lam _ d b _ | .forallE _ d b _ => return (← occ t pk memo d ctx) ++ (← occ t pk memo b ctx)
  | .letE _ ty v b _ =>
    return (← occ t pk memo ty ctx) ++ (← occ t pk memo v ctx) ++ (← occ t pk memo b ctx)
  | .mdata _ b => occ t pk memo b ctx
  | _ => return #[]

def run : MetaM Unit := do
  let env ← getEnv
  let cls := roots.map fun r => (r, closure env r)
  for (r, c) in cls do
    let mods : NameSet := c.fold (init := {}) fun s n _ => s.insert (moduleOf env n)
    let thms := c.fold (init := 0) fun k n _ =>
      match env.find? n with | some (.thmInfo _) => k + 1 | _ => k
    IO.println s!"root {r}: {c.size} project constants ({thms} theorems) in {mods.size} modules"
  let inAny (n : Name) : String :=
    let l := cls.toList.filterMap fun (r, c) => if c.contains n then some r.getString! else none
    if l.isEmpty then "none" else ", ".intercalate l
  let inAnyB (n : Name) : Bool := cls.any fun (_, c) => c.contains n
  -- Q1
  IO.println "\n== Q1 HealthyBaseU"
  let hbs := resolveSuffix env `HealthyBaseU
  for hb in hbs do
    IO.println s!"structure {hb} [{moduleOf env hb}]"
    let fam := env.constants.fold (init := #[hb]) fun acc n _ =>
      if hb.isPrefixOf n && n != hb && isProject env n then acc.push n else acc
    IO.println s!"  family ({fam.size} constants: projections, mk, rec, casesOn, …):"
    for f in fam.qsort Name.lt do IO.println s!"    {f}: reached by {inAny f}"
    for (r, c) in cls do
      let users := c.fold (init := #[]) fun acc n _ =>
        if (edges env n).any (fam.contains ·) then acc.push n else acc
      IO.println s!"  {r.getString!}: users of the family in the closure: {users.size}"
      for u in users do IO.println s!"    path: {fmtPath env (pathTo c u)}"
  for nm in [`awake, `syncAC, `two_faulty_lt] do
    for (r, c) in cls do
      let hits := c.fold (init := #[]) fun acc n _ =>
        if (userName n).isStr && (userName n).getString! == nm.getString! then acc.push n else acc
      IO.println s!"  reached `{nm}` constants from {r.getString!}: {hits.qsort Name.lt}"
  -- Q2
  IO.println "\n== Q2 trace_mayVote_stock"
  for t in resolveSuffix env `trace_mayVote_stock do
    IO.println s!"{t} [{moduleOf env t}]: reached by {inAny t}"
    let callers := env.constants.fold (init := #[]) fun acc n _ =>
      if isProject env n && n != t && (edges env n).contains t then acc.push n else acc
    IO.println s!"  direct users ({callers.size}):"
    for u in callers.qsort Name.lt do IO.println s!"    {userName u} [{moduleOf env u}]: reached by {inAny u}"
  for m in [`ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial,
      `ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FreshLock,
      `ConsensusLeanTest.Goldilocks.Regimes.ProposerHoldRun.Cast] do
    let some idx := env.getModuleIdx? m | throwError "module {m} not loaded"
    let names := env.header.moduleData[idx.toNat]!.constNames
    let reached := names.filter inAnyB
    IO.println s!"module {m}: {names.size} constants, reached {reached.size} {reached.map userName}"
  -- Q3
  IO.println "\n== Q3 source_compatible_at"
  for s in resolveSuffix env `Compose.Growing.source_compatible_at do
    let some ci := env.find? s | continue
    IO.println s!"{s} [{moduleOf env s}]: reached by {inAny s}"
    for (r, c) in cls do
      if c.contains s then IO.println s!"  path from {r.getString!}: {fmtPath env (pathTo c s)}"
    IO.println s!"  signature: {← ppExpr ci.type}"
    let bad := [`committeeSize, `SourceCompatible, `source_compatible, `source_compatible_stored]
    let isBad (n : Name) : Bool := (userName n).isStr && bad.any (·.getString! == (userName n).getString!)
    let tyHits := (refs ci.type).toArray.filter isBad
    let own := edges env s
    let ownHits := own.filter isBad
    -- its own auxiliaries
    let aux := (closure env s).fold (init := #[]) fun acc n _ =>
      if s.isPrefixOf n && n != s then acc.push n else acc
    let auxHits := aux.foldl (fun acc a => acc ++ (edges env a).filter isBad) #[]
    let tc := closure env s
    let transHits := tc.fold (init := #[]) fun acc n _ => if isBad n then acc.push n else acc
    IO.println s!"  type mentions: {tyHits}"
    IO.println s!"  type+value (direct) mentions: {ownHits}; own aux {aux}: {auxHits}"
    IO.println s!"  its own transitive closure ({tc.size}) contains: {transHits.qsort Name.lt}"
    for h in transHits do IO.println s!"    path: {fmtPath env (pathTo tc h)}"
    let stockHits := tc.fold (init := #[]) fun acc n _ =>
      if (userName n).isStr && (userName n).getString! == "stock" then acc.push n else acc
    IO.println s!"  `*.stock` constants in its own closure: {stockHits.qsort Name.lt}"
    for h in stockHits do IO.println s!"    path: {fmtPath env (pathTo tc h)}"
  for (r, c) in cls do
    let stockHits := c.fold (init := #[]) fun acc n _ =>
      if (userName n).isStr && (userName n).getString! == "stock" then acc.push n else acc
    IO.println s!"`*.stock` constants in the closure of {r.getString!}: {stockHits.qsort Name.lt}"
    for h in stockHits do IO.println s!"    path: {fmtPath env (pathTo c h)}"
  -- Q4/Q5
  let G := `ConsensusLean.Instances.Goldilocks.Lemmas
  let sites : List (String × Name × Nat) := [
    ("Q4", G ++ `Compose.Service.PivotBase, 454),
    ("Q4", G ++ `Compose.Service.SuffixWindow, 147),
    ("Q4", G ++ `Compose.Sleepy.FrameLabels, 193),
    ("Q4", G ++ `Compose.Sleepy.FrameLabels, 240),
    ("Q4", G ++ `Growing.Healing.Report.OptimisticBaseVotes, 79),
    ("Q4", G ++ `Growing.Healing.Report.OptimisticBaseVotes, 80),
    ("Q4", G ++ `Growing.Healing.Report.RegularTransfer, 90),
    ("Q4", G ++ `Growing.Healing.Report.RegularTransfer, 93),
    ("Q5", G ++ `Growing.Outage.Engine.ArmingSteps, 381),
    ("Q5", G ++ `Growing.Outage.Engine.ArmingSteps, 421),
    ("Q5", G ++ `Growing.Sleepy.Node.LiftFrame, 43),
    ("Q5", G ++ `Obligations.OutageArmingSteps, 478),
    ("Q5", G ++ `Growing.Sleepy.Node.TransferLocks, 90),
    ("Q5", G ++ `Growing.Sleepy.Node.TransferFirst, 71),
    ("Q5", G ++ `Growing.Sleepy.Node.Frame, 154),
    ("Q5", G ++ `Growing.Sleepy.Node.VoteFrame, 213),
    ("Q5", G ++ `Growing.Outage.Locks, 139),
    ("Q5", G ++ `Obligations.OutageLockSafety.Prot, 88)]
  IO.println "\n== Q4/Q5 sites"
  for (q, m, line) in sites do
    let src ← sourceLine m line
    let some (d, a, b) ← enclosing m line
      | IO.println s!"{q} {fileOf m}:{line}: NO ENCLOSING DECLARATION | {src}"
    let auxReached := env.constants.fold (init := #[]) fun acc n _ =>
      if d.isPrefixOf n && n != d && inAnyB n then acc.push n else acc
    IO.println s!"{q} {fileOf m}:{line} | {src}\n    decl {userName d} (lines {a}–{b}): reached by {inAny d}; reached aux of it: {auxReached}"
    for (r, c) in cls do
      if c.contains d then IO.println s!"    path from {r.getString!}: {fmtPath env (pathTo c d)}"
    let ls := (← IO.FS.readFile (fileOf m)).splitOn "\n"
    for l in [a:b+1] do
      let s := ls.getD (l - 1) ""
      if (s.splitOn "stock").length > 1 then IO.println s!"    src {fileOf m}:{l}: {s.trimAscii}"
  -- Q6: every reached use of a `stock` constant / `mayVote_stock` family
  IO.println "\n== Q6 reached uses of `*.stock`, `trace_mayVote_stock`, `mayVote_stock(_at)`"
  let union : NameSet := cls.foldl (fun s (_, c) => c.fold (fun s n _ => s.insert n) s) {}
  let hitNames := ["stock", "trace_mayVote_stock", "mayVote_stock", "mayVote_stock_at"]
  let hits := (env.constants.fold (init := #[]) fun acc n _ =>
    if isProject env n && (userName n).isStr && hitNames.contains (userName n).getString! &&
      (union.contains n || ((projKey env n).map fun p => union.contains p.1).getD false)
    then acc.push n else acc).qsort Name.lt
  IO.println s!"candidate hit constants (reached, or a projection of a reached structure): {hits}"
  let anyPath (n : Name) : String := Id.run do
    for (r, c) in cls do
      if c.contains n then return s!"from {r.getString!}: {fmtPath env (pathTo c n)}"
    return "unreached"
  for t in hits do
    let pk := projKey env t
    IO.println s!"\n-- {t} [{moduleOf env t}] (primitive projection key {pk}): reached by {inAny t}"
    let mut users := #[]
    for u in union.toArray.qsort Name.lt do
      if u == t then continue
      let some ci := env.find? u | continue
      let memo ← IO.mkRef ({} : Std.HashMap Expr Bool)
      let (es, _) := exprsOf env ci
      let mut hit := false
      for e in es do
        if ← mentions t pk memo e then hit := true
      if hit then users := users.push u
    IO.println s!"   reached direct users: {users.size}"
    for u in users do
      let (o, a, b) ← owner u
      let m := moduleOf env o
      IO.println s!"   * {userName u}  (owner {userName o}, {fileOf m}:{a}–{b}); reached by {inAny u}"
      IO.println s!"     path {anyPath u}"
      if a > 0 then
        let ls := (← IO.FS.readFile (fileOf m)).splitOn "\n"
        for l in [a:b+1] do
          let s := ls.getD (l - 1) ""
          if (s.splitOn "stock").length > 1 then IO.println s!"     src {fileOf m}:{l}: {s.trimAscii}"
      let some ci := env.find? u | continue
      let memo ← IO.mkRef ({} : Std.HashMap Expr Bool)
      let (es, _) := exprsOf env ci
      let mut seenCtx : Std.HashSet String := {}
      for e in es do
        for c in ← occ t pk memo e "outside any record field" do
          unless seenCtx.contains c do
            seenCtx := seenCtx.insert c
            IO.println s!"     occurrence: {c}"

end ElabReach

#eval ElabReach.run
