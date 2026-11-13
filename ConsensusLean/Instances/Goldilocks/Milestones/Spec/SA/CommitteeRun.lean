module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Events
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Committee

@[expose] public section

/-! # Goldilocks SA: a slot committee over an SA trace

The committee facts the committee-native AC step statements take, for a slot dictionary
`K : CommitteeDict sp.n` of an AC trace with honest set `H`:

* **P** (`CommitteeP`): the votes in the pools of honest nodes, and in the states at which an honest
  node runs the optimistic check, are signed by members of their slot's committee.
* **T** (`CommitteeT`): the votes in the merged vote view of an honest vote are signed by members
  of their slot's committee.
* **CS** (`FaultBoundK`): among the members of the slot-`s` committee, fewer are faulty than are
  honest, awake and joined at `t`.

Thresholds stay in `sp.committeeSize`; a caller binds `K` to it by `(K.committee s).ncard =
sp.committeeSize`. At `K = CommitteeDict.full sp.n` with `sp.committeeSize = sp.n`, P and T hold
for every signer and CS is `FaultBound tr H t`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

/-- **P**: honest pools and optimistic-check states hold only signatures of the slot's
committee. -/
def CommitteeP (K : CommitteeDict sp.n) (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) : Prop :=
  (∀ y ∈ H, ∀ (i s : Nat), ∀ v ∈ (tr.state y i).pool s, v.val ∈ K.committee s) ∧
  (∀ y ∈ H, ∀ i ℓ A, OptimisticPoint tr y i ℓ A → ∀ s : Nat, ∀ v ∈ A.pool s,
    v.val ∈ K.committee s)

/-- **T**: the merged-view votes of an honest vote, block payload votes included, are signed by
members of their slot's committee. -/
def CommitteeT (K : CommitteeDict sp.n) (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) : Prop :=
  ∀ y ∈ H, ∀ i ℓ e, CastAt tr y i ℓ e → ∀ m : Nat,
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (m + 1)).votes, v.val ∈ K.committee v.slot

/-- **CS** at the slot-`s` committee, with the faults charged at `t`. -/
def FaultBoundK (K : CommitteeDict sp.n) (s : Nat) (tr : SATrace sp FGP ro)
    (H : Set (Fin sp.n)) (t : Time) : Prop :=
  (K.committee s ∩ Hᶜ).ncard <
    (K.committee s ∩ {y | y ∈ H ∧ tr.awake y t ∧ JoinedAt tr y t}).ncard

end Consensus.Goldilocks.SA

end
