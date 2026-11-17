import Lean
/-!
# Elaborated stock-dependence check

The certifying reach check of `scripts/stock-reach.py`, which composes a driver from the files to
check (their imports first; `StockReachControls.lean` for the project, a fixture otherwise) and
this file, and sets the configuration in the environment:

* `SR_ROOTS`: the roots, full names (a private root by its user name);
* `SR_LIST`: the stock-only list, one `full name<TAB>module` per line;
* `SR_SETUP`: the setup type; `SR_STOCK`: the stock constants;
* `SR_PROJECT`: module prefixes of the project (declarations of the driver itself count too);
* `SR_CONTROLS`: `name:+` (must be flagged) / `name:-` (must not), checked by the flag rule below;
* `SR_QUERY`: declarations whose membership and path to report.

Closure, per root: breadth-first over the elaborated environment. The edges of a constant are the
constants occurring in its type, its value (`def`/`theorem`/`opaque`; proofs included), the types of
its constructors (an inductive), its inductive (a constructor) and its rule right-hand sides (a
recursor), counting the structure of every primitive projection. Only project constants are kept.

Verdict, per root: the closure contains no listed constant, and no reached constant is *flagged*: a
binder of the setup type in its type's ∀-telescope, and a stock or listed constant among the
constants of its type, value or constructors, or of its own auxiliary constants (`c.proof_n`,
`c.match_n`, `where` helpers). A listed entry or root that does not resolve, a control with the
wrong verdict, or a reached axiom of the project fails. Prints `[reach] verdict: PASS` or fails.
-/

open Lean

namespace StockReach

def envList (k : String) : IO (Array String) := do
  return (((← IO.getEnv k).getD "").splitOn ",").toArray.filter (· ≠ "")

def moduleOf (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.map fun i => env.header.moduleNames[i.toNat]!

def userName (n : Name) : Name := (privateToUserName? n).getD n

/-- Constants and projected structures occurring in `e`. -/
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

/-- The expressions of `ci`, and the constants it refers to outside them. -/
def exprsOf (env : Environment) (ci : ConstantInfo) : Array Expr × Array Name :=
  match ci with
  | .defnInfo v => (#[v.type, v.value], #[])
  | .thmInfo v => (#[v.type, v.value], #[])
  | .opaqueInfo v => (#[v.type, v.value], #[])
  | .inductInfo v => (#[v.type] ++ v.ctors.toArray.filterMap fun c => (env.find? c).map (·.type), #[])
  | .ctorInfo v => (#[v.type], #[v.induct])
  | .recInfo v => (#[v.type] ++ v.rules.toArray.map (·.rhs), #[])
  | ci => (#[ci.type], #[])

def refsOf (env : Environment) (n : Name) : NameSet := Id.run do
  let some ci := env.find? n | return {}
  let (es, extra) := exprsOf env ci
  let mut s : NameSet := extra.foldl (·.insert ·) {}
  for e in es do s := (refs e).foldl (·.insert ·) s
  return s

/-- BFS closure from `root` over `isProject` constants, with parent pointers. -/
def closure (env : Environment) (isProject : Name → Bool) (root : Name) : Std.HashMap Name Name :=
  Id.run do
  let mut parent : Std.HashMap Name Name := ({} : Std.HashMap Name Name).insert root root
  let mut frontier := #[root]
  while !frontier.isEmpty do
    let mut next := #[]
    for n in frontier do
      for u in (refsOf env n).toArray.qsort Name.lt do
        unless isProject u && !parent.contains u do continue
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

/-- A binder of type `setup` in the ∀-telescope. -/
partial def setupBinder (setup : Name) : Expr → Bool
  | .forallE _ d b _ => d.cleanupAnnotations.isConstOf setup || setupBinder setup b
  | .mdata _ e => setupBinder setup e
  | _ => false

/-- Constants used by `c` and by its own auxiliary constants. -/
def usedBy (env : Environment) (c : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  let mut todo := #[c]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    for u in refsOf env n do
      out := out.insert u
      if u != c && c.isPrefixOf u && !seen.contains u then todo := todo.push u
  return out

def run : CoreM Unit := do
  let env ← getEnv
  let some listPath ← IO.getEnv "SR_LIST" | throwError "SR_LIST unset"
  let setup := ((← IO.getEnv "SR_SETUP").getD "").toName
  let stock := (← envList "SR_STOCK").map String.toName
  let prefixes := (← envList "SR_PROJECT").map String.toName
  let isProject (n : Name) : Bool := match moduleOf env n with
    | some m => prefixes.any (·.isPrefixOf m)
    | none => env.contains n
  -- private project constants by user name
  let mut priv : Std.HashMap Name Name := {}
  for i in [:env.header.moduleNames.size] do
    if prefixes.any (·.isPrefixOf env.header.moduleNames[i]!) then
      for n in env.header.moduleData[i]!.constNames do
        if let some u := privateToUserName? n then priv := priv.insert u n
  let resolve (s : String) : Option Name :=
    let n := s.toName
    if env.contains n then some n else priv.get? n
  let mut failed := false
  unless env.contains setup do throwError "setup type {setup} not in the environment"
  for s in stock do unless env.contains s do throwError "stock constant {s} not in the environment"
  -- the list
  let mut listed : Array Name := #[]
  for l in (← IO.FS.readFile listPath).splitOn "\n" do
    let [nm, mod] := l.splitOn "\t" | continue
    match resolve nm with
    | none => IO.println s!"[reach] unresolved listed declaration {nm}"; failed := true
    | some n =>
      if let some m := moduleOf env n then
        unless m == mod.toName do
          IO.println s!"[reach] listed {nm} is in {m}, not {mod}"; failed := true
      listed := listed.push n
  IO.println s!"[reach] listed constants: {listed.size}"
  let bad : NameSet := (stock ++ listed).foldl (·.insert ·) {}
  let listedSet : NameSet := listed.foldl (·.insert ·) {}
  let flag (n : Name) : Option (Bool × Array Name) := do
    let ci ← env.find? n
    return (setupBinder setup ci.type, (usedBy env n).toArray.filter (bad.contains ·) |>.qsort Name.lt)
  -- controls
  for c in ← envList "SR_CONTROLS" do
    let [nm, sign] := c.splitOn ":" | throwError "bad control {c}"
    let some n := resolve nm | throwError "control {nm} not in the environment"
    let some (sb, off) := flag n | throwError "control {nm} not in the environment"
    let flagged := sb && !off.isEmpty
    let ok := flagged == (sign == "+")
    unless ok do failed := true
    IO.println s!"[reach] control {n}: setupBinder={sb} uses={off} → \
      {if flagged then "FLAGGED" else "pass"} ({if ok then "ok" else "CONTROL FAILED"})"
  let fmt (n : Name) : String := s!"{userName n} [{(moduleOf env n).getD `«driver»}]"
  let queries ← envList "SR_QUERY"
  for r in ← envList "SR_ROOTS" do
    let some root := resolve r
      | IO.println s!"[reach] root {r}: not in the environment"; failed := true; continue
    let cl := closure env isProject root
    let mut flagged := #[]
    let mut hits := #[]
    let mut axioms := #[]
    for (n, _) in cl.toArray.qsort (fun a b => Name.lt a.1 b.1) do
      if listedSet.contains n then hits := hits.push n
      if let some (.axiomInfo _) := env.find? n then axioms := axioms.push n
      if let some (true, off) := flag n then
        unless off.isEmpty do flagged := flagged.push (n, off)
    IO.println s!"[reach] root {root}: reached={cl.size} listed={hits.size} flagged={flagged.size} \
      axioms={axioms.size}"
    let showPath (n : Name) : IO Unit := do
      for p in pathTo cl n do IO.println s!"        {fmt p}"
    for n in hits do
      IO.println s!"    LISTED {fmt n}"; showPath n
    for (n, off) in flagged do
      IO.println s!"    FLAG {fmt n} ← {off}"; showPath n
    for n in axioms do IO.println s!"    AXIOM {fmt n}"
    for q in queries do
      let qs := (cl.toArray.map (·.1)).filter fun n => q.toName.isSuffixOf (userName n)
      if qs.isEmpty then IO.println s!"    query {q}: not reached"
      for n in qs do
        IO.println s!"    query {q}: REACHED as {fmt n}"; showPath n
    unless hits.isEmpty && flagged.isEmpty && axioms.isEmpty do failed := true
  if failed then
    IO.println "[reach] verdict: FAIL"
    throwError "stock-dependence reach check failed"
  IO.println "[reach] verdict: PASS"

end StockReach

#eval StockReach.run
