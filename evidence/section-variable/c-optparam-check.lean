import ConsensusLean.Instances.Goldilocks.AsChainShape
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
import ConsensusLean.Lemmas.Model.Objects
open Lean Elab Command

/-! Strip-optParam comparison for the AsChainShape section variable, plus the type check for the
moved `installVote_eq_mayVote`. Run with `lake env lean` in the built worktree at the amended commit. -/

/-- Strip `optParam` from the binder types of the leading lambdas. -/
partial def stripLead : Expr → Expr
  | .lam n t b bi => .lam n t.consumeTypeAnnotations (stripLead b) bi
  | e => e

/-- Value hashes of the 26 definitions in the parent commit's scripts/instance-spec-snapshot.txt. -/
def oldHashes : List (Name × UInt64) := [
  (`Consensus.Goldilocks.AsChainShape.IsAttObj, 3173222568),
  (`Consensus.Goldilocks.AsChainShape.apply, 3370398362),
  (`Consensus.Goldilocks.AsChainShape.attObj, 2900818675),
  (`Consensus.Goldilocks.AsChainShape.blockObj, 3774763344),
  (`Consensus.Goldilocks.AsChainShape.canonEvent, 3636392709),
  (`Consensus.Goldilocks.AsChainShape.conflicts, 2275202749),
  (`Consensus.Goldilocks.AsChainShape.decodeAttObj, 4162782420),
  (`Consensus.Goldilocks.AsChainShape.decodeBlock, 800171956),
  (`Consensus.Goldilocks.AsChainShape.decodeVoteObj, 1052448496),
  (`Consensus.Goldilocks.AsChainShape.delivered, 81304459),
  (`Consensus.Goldilocks.AsChainShape.fgUpdate, 2679473495),
  (`Consensus.Goldilocks.AsChainShape.forwardObj, 2261724180),
  (`Consensus.Goldilocks.AsChainShape.forwardParent?, 1858530694),
  (`Consensus.Goldilocks.AsChainShape.isFGAtt, 2209564624),
  (`Consensus.Goldilocks.AsChainShape.nodeTick, 821537297),
  (`Consensus.Goldilocks.AsChainShape.payloadObjs, 2193728946),
  (`Consensus.Goldilocks.AsChainShape.poll, 3827642591),
  (`Consensus.Goldilocks.AsChainShape.pollBatch, 1361043783),
  (`Consensus.Goldilocks.AsChainShape.process, 1051931326),
  (`Consensus.Goldilocks.AsChainShape.processOne, 3700177894),
  (`Consensus.Goldilocks.AsChainShape.propose, 1654435988),
  (`Consensus.Goldilocks.AsChainShape.queueAccepted, 2193970879),
  (`Consensus.Goldilocks.AsChainShape.recordOwn, 3065203484),
  (`Consensus.Goldilocks.AsChainShape.relayIf, 3496529543),
  (`Consensus.Goldilocks.AsChainShape.restore, 2734205620),
  (`Consensus.Goldilocks.AsChainShape.voteObj, 516067500)]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut ok : Nat := 0
  for (n, h) in oldHashes do
    let ci := (env.find? n).get!
    let v := ci.value!
    let s := stripLead v
    let typeHasOptParam := ci.type.find? (fun e => e.isAppOfArity ``optParam 2) |>.isSome
    if s.hash == h then ok := ok + 1
    logInfo m!"{n}: raw {v.hash} stripped {s.hash} parent {h} {if s.hash == h then "MATCH" else "MISMATCH"} (type keeps optParam: {typeHasOptParam})"
  logInfo m!"{ok}/{oldHashes.length} match the parent hash after stripping optParam from the leading binders"

/-! The Lemmas-side declaration as it stood in the parent (Lemmas/Simulation/Shape.lean:42-46),
re-elaborated verbatim in its original namespace and opens. -/
namespace Consensus.Goldilocks.Simulation
open AsChainShape
open Blocks Shape
open SA (SAParams ReplayOrder Vote Payload)
variable {binding : VoteBinding}

theorem installVote_eq_mayVote (B : VoteBinding) {n : Nat} (p : ShapeRole B.Kind → Bool)
    (a : SA.SAState n) : B.installVote p a = { a with mayVote := (B.installVote p a).mayVote } := by
  unfold VoteBinding.installVote
  split <;> rfl

end Consensus.Goldilocks.Simulation

#eval show CommandElabM Unit from do
  let env ← getEnv
  let old := (env.find? `Consensus.Goldilocks.Simulation.installVote_eq_mayVote).get!
  let new := (env.find? `Consensus.Goldilocks.AsChainShape.VoteBinding.installVote_eq_mayVote).get!
  logInfo m!"installVote_eq_mayVote: old type hash {old.type.hash} new type hash {new.type.hash} levels {old.levelParams}/{new.levelParams} types equal: {old.type == new.type}"
