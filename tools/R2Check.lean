import ConsensusLean
import ConsensusLeanTest
/-! records(2) closure checks: the 7 milestone statements, the Fact scaffolding constants, the run-record
`stock` fields, and whether `AsChainShape.stock` is reached other than through `AsChainShape.goldilocks`. -/
set_option autoImplicit false
open Lean Meta

namespace R2C

def roots : Array Name :=
  #[`Consensus.Goldilocks.Obligations.Growing.outage_protected_at,
    `Consensus.Goldilocks.Obligations.Growing.meetsObligations_persists_growing]

def watch : Array Name :=
  #[`Consensus.Goldilocks.Compose.HeadExtendsRecord, `Consensus.Goldilocks.Compose.Inclusion,
    `Consensus.Goldilocks.Regimes.SleepySafe, `Consensus.Goldilocks.Regimes.IncludeSleepy,
    `Consensus.Goldilocks.Regimes.GrowSleepy, `Consensus.Goldilocks.Healing.HeightScopedRetention,
    `Consensus.Goldilocks.Healing.RunInclusion,
    `Consensus.Goldilocks.SA.ACHealingStandaloneAll, `Consensus.Goldilocks.SA.ACInclusionAll,
    `Consensus.Goldilocks.Generic.GoldilocksHealingData,
    `Consensus.Goldilocks.Simulation.stock_participationKind_none,
    `Consensus.Goldilocks.Simulation.committeeSize_of_participationKind_none,
    `Consensus.Goldilocks.GoldilocksRun.stock, `Consensus.Goldilocks.Growing.GoldilocksRun.stock,
    `Consensus.Goldilocks.SA.ACRun.stock, `Consensus.Goldilocks.SA.ACRunU.stock,
    `Consensus.Goldilocks.SA.ACRunUS.stock, `Consensus.Goldilocks.SA.Growing.ACRun.stock,
    `Consensus.Goldilocks.Compose.OutageLockPremises.stock,
    `Consensus.Goldilocks.AsChainShape.stock,
    `Consensus.Goldilocks.Healing.high_vote_extends_of_syncAC,
    `Consensus.Goldilocks.Healing.high_vote_extends,
    `Consensus.Goldilocks.Compose.Growing.ReadyImpliesJoined,
    `Consensus.Goldilocks.Compose.Growing.HeadExtendsRecord,
    `Consensus.Goldilocks.Compose.Growing.Inclusion,
    `Consensus.Goldilocks.Compose.Growing.OutcomeService,
    `Consensus.Goldilocks.Healing.Growing.CutAndReset,
    `Consensus.Goldilocks.Healing.Growing.ResetExistence,
    `Consensus.Goldilocks.Healing.Growing.NonInterference,
    `Consensus.Goldilocks.Healing.Growing.AvailableHealing,
    `Consensus.Goldilocks.Healing.Growing.ViableWitnessRetention,
    `Consensus.Goldilocks.Healing.Growing.CleanLockDrain,
    `Consensus.Goldilocks.Healing.Growing.FrozenTreeAgreement,
    `Consensus.Goldilocks.Healing.Growing.CommonPathAcquisition,
    `Consensus.Goldilocks.Healing.Growing.PatternRecovery,
    `Consensus.Goldilocks.Healing.Growing.FinalizingCoverage,
    `Consensus.Goldilocks.Healing.Growing.CacheAcceptanceAfterReset,
    `Consensus.Goldilocks.Regimes.Growing.SleepySafe,
    `Consensus.Goldilocks.Regimes.Growing.IncludeSleepy,
    `Consensus.Goldilocks.Regimes.Growing.GrowSleepy,
    `Consensus.Goldilocks.SA.Growing.ACHealingStandalone,
    `Consensus.Goldilocks.SA.Growing.ACHealingStandaloneCorollary,
    `Consensus.Goldilocks.SA.Growing.ACInclusion,
    `Consensus.Goldilocks.Healing.Growing.HeightScopedRetention,
    `Consensus.Goldilocks.Healing.Growing.RunInclusion,
    `Consensus.Goldilocks.Compose.Growing.GoldilocksACProjection,
    `Consensus.Goldilocks.Compose.Growing.HonestFastConfirmationsPersist,
    `Consensus.Goldilocks.Compose.Growing.JoinedProjection,
    `Consensus.Goldilocks.Compose.Growing.RecentSourceNextVote,
    `Consensus.Goldilocks.Regimes.Growing.FinalAccountable,
    `Consensus.Goldilocks.Regimes.Growing.FinalizedMonotone,
    `Consensus.Goldilocks.Regimes.Growing.FinalizedSafe,
    `Consensus.Goldilocks.Regimes.Growing.NonFraming,
    `Consensus.Goldilocks.Regimes.Growing.OutputsNested,
    `Consensus.Goldilocks.Regimes.Growing.OutputsValid]

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

def isProject (env : Environment) (n : Name) : Bool :=
  (`ConsensusLean).isPrefixOf (moduleOf env n) || (`ConsensusLeanTest).isPrefixOf (moduleOf env n)

partial def collect (e : Expr) : NameSet := Id.run do
  let mut cs : NameSet := {}
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
    | .proj s _ b => cs := cs.insert s; todo := todo.push b
    | _ => pure ()
  return cs

def uses (env : Environment) (ci : ConstantInfo) : NameSet := Id.run do
  let es : Array Expr × Array Name := match ci with
    | .defnInfo v => (#[v.type, v.value], #[])
    | .thmInfo v => (#[v.type, v.value], #[])
    | .opaqueInfo v => (#[v.type, v.value], #[])
    | .inductInfo v => (#[v.type] ++ v.ctors.toArray.filterMap fun c => (env.find? c).map (·.type), #[])
    | .ctorInfo v => (#[v.type], #[v.induct])
    | .recInfo v => (#[v.type] ++ v.rules.toArray.map (·.rhs), #[])
    | ci => (#[ci.type], #[])
  let mut s : NameSet := es.2.foldl (·.insert ·) {}
  for e in es.1 do s := (collect e).foldl (·.insert ·) s
  return s

def closureP (env : Environment) (root : Name) (block : NameSet) : Std.HashMap Name Name := Id.run do
  let mut par : Std.HashMap Name Name := ({} : Std.HashMap Name Name).insert root root
  let mut frontier := #[root]
  while !frontier.isEmpty do
    let mut next := #[]
    for n in frontier do
      let some ci := env.find? n | continue
      for u in uses env ci do
        if isProject env u && !par.contains u && !block.contains u then
          par := par.insert u n
          next := next.push u
    frontier := next
  return par

def closure (env : Environment) (root : Name) (block : NameSet) : NameSet :=
  (closureP env root block).fold (init := {}) fun s k _ => s.insert k

def pathTo (par : Std.HashMap Name Name) (t : Name) : List Name := Id.run do
  let mut out := [t]
  let mut cur := t
  for _ in [:200] do
    let p := par.getD cur cur
    if p == cur then break
    out := p :: out
    cur := p
  return out

def run : MetaM Unit := do
  let env ← getEnv
  let factPk := env.constants.fold (init := #[]) fun acc n ci =>
    if isProject env n then
      let cs := collect ci.type
      if cs.contains ``Fact && cs.toList.any (fun c => c.toString.endsWith "participationKind") then
        acc.push n else acc
    else acc
  IO.println s!"Fact-participationKind constants in the environment: {factPk.size} {factPk.toList.take 20}"
  for r in roots do
    let c := closure env r {}
    let cNoHead := closure env r (({} : NameSet).insert `Consensus.Goldilocks.AsChainShape.goldilocks)
    IO.println s!"\n== {r}: {c.size} constants"
    for w in watch do
      let present := env.contains w
      IO.println s!"  {w}: {if !present then "absent" else if c.contains w then "REACHED" else "unreached"}"
    IO.println s!"  Fact-participationKind reached: {(factPk.filter c.contains).size}"
    IO.println s!"  AsChainShape.stock reached with AsChainShape.goldilocks blocked: {cNoHead.contains `Consensus.Goldilocks.AsChainShape.stock}"
    let par := closureP env r {}
    for w in watch do
      if par.contains w && w != `Consensus.Goldilocks.AsChainShape.stock then
        IO.println s!"  PATH {w}: {pathTo par w}"
    let parNH := closureP env r (({} : NameSet).insert `Consensus.Goldilocks.AsChainShape.goldilocks)
    if parNH.contains `Consensus.Goldilocks.AsChainShape.stock then
      IO.println s!"  PATH (goldilocks blocked) AsChainShape.stock: {pathTo parNH `Consensus.Goldilocks.AsChainShape.stock}"
    let fields := c.toList.filter fun n =>
      (n.isStr && (n.getString! == "stock" || n.getString! == "hmv")) && (env.getProjectionFnInfo? n).isSome
    IO.println s!"  structure stock/hmv projections reached: {fields.length} {fields}"
    let structs := c.toList.filter fun n =>
      isStructure env n && ((getStructureFields env n).contains `stock || (getStructureFields env n).contains `hmv)
    IO.println s!"  reached structures with a stock/hmv field: {structs.length} {structs}"

end R2C

#eval R2C.run
