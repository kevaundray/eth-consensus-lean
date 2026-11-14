module
import all ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMap

namespace Consensus.Goldilocks.Simulation
open AsChainShape Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] (S : BoundSetup) {E : Env V}
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)
  (hv : rho.ExecutionValid)

/-- The run map's chain up to a tip is `blocksTo` with the tip's slot as fuel (the field's
definition, `RunMap.lean:68`; g0a5 has no characterising lemma for `chain`). -/
theorem f1_goldilocksRunMap_chain (hv : rho.ExecutionValid)
    (st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _)))
    (B : Blk (S.params (pubOf E) hn)) :
    (goldilocksRunMap S rho hn hv).chain st B = blocksTo st.fg.blocks (B.slot + 1) B := by rfl

/-- With `chain := blocksTo`, a non-genesis tip is in its own chain whether or not it is held,
so `ReadRepresentation.chain_held` fails for `goldilocksRunMap`. -/
theorem scratch_not_readRepresentation :
    ¬ Generic.ReadRepresentation (goldilocksRunMap S rho hn hv) := by
  intro h
  let st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _)) :=
    (simTraceAt S rho hn).state ⟨0, hn⟩ 0
  let X : Nat → Blk (S.params (pubOf E) hn) := fun s =>
    { root := (S.params (pubOf E) hn).genesisRoot + 1, parent := none, slot := s,
      proposer := ⟨0, hn⟩, input := 0, fgPayload := [],
      acPayload := (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload }
  have hroot : ∀ s, ¬ (X s).root = (S.params (pubOf E) hn).genesisRoot := fun s =>
    Nat.succ_ne_self _
  have hmem : ∀ s, X s ∈ st.fg.tree := fun s => by
    apply h.chain_held st (X s)
    rw [f1_goldilocksRunMap_chain, blocksTo_succ, if_neg (hroot s)]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have h0 : st.fg.blocks ((S.params (pubOf E) hn).genesisRoot + 1) = some (X 0) := hmem 0
  have h1 : st.fg.blocks ((S.params (pubOf E) hn).genesisRoot + 1) = some (X 1) := hmem 1
  have h01 : (0 : Nat) = 1 :=
    congrArg Block.slot (Option.some.inj (h0.symm.trans h1))
  exact Nat.zero_ne_one h01

#print axioms scratch_not_readRepresentation

end Consensus.Goldilocks.Simulation
