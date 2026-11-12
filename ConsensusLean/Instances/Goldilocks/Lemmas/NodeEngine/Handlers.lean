module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Engine

public section

/-! # Node engine handlers: the node state

The engine's handlers change the node state (`State.node`) exactly as the node's handlers do:
* a delivered object whose canonical event is a block, an AC message or an attestation runs
  `Node.onBlock`, `Node.onMessage` or `Node.onAttestation` (`processOne_node_block`,
  `processOne_node_message`, `processOne_node_attestation`); with no canonical event it keeps
  the node state (`processOne_node_none`);
* the node's tick runs `Node.acCall … .tick` at a public time and keeps the node state at
  another time (`nodeTick_node_public`, `nodeTick_node_other`);
* the slot proposal runs `Node.acProposal` (`propose_node`);
* the FG update runs `Node.acToFG` and then `Node.attest`, the node's `tickStep .fgUpdate`
  (`fgUpdate_node`);
* recording an own block runs `Node.onBlock` on the block it decodes (`recordOwn_node_block`).

The engine's own wrappers, queues, relay buffer and clock are not described here. -/

namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape
open Consensus.Model (Public)

variable {pub : Public} {hn : 1 ≤ pub.n} {S M Q Info Body : Type}
  [DecidableEq Info] [Countable Info] {R : Runtime pub hn S M Q} (W : Wire R Info Body)

/-! ## Deliveries -/

/-- A delivered object whose canonical event is a block runs `on_block`. -/
theorem processOne_node_block (hs : List (Header Info × Nat)) (st : State W)
    (o : ShapeObj pub.n Empty Info Body) {B} (h : W.canonEvent hs o = some (.block B)) :
    (processOne W hs st o).node = (Node.onBlock st.self st.node st.now B).1 := by
  simp only [processOne, h]
  split <;> rfl

/-- A delivered object whose canonical event is an AC message runs `on_ac_message`. -/
theorem processOne_node_message (hs : List (Header Info × Nat)) (st : State W)
    (o : ShapeObj pub.n Empty Info Body) {m} (h : W.canonEvent hs o = some (.message m)) :
    (processOne W hs st o).node = (Node.onMessage st.self st.node st.now m).1 := by
  unfold processOne
  rw [h]
  rfl

/-- A delivered object whose canonical event is an attestation runs `on_attestation`. -/
theorem processOne_node_attestation (hs : List (Header Info × Nat)) (st : State W)
    (o : ShapeObj pub.n Empty Info Body) {a} (h : W.canonEvent hs o = some (.attestation a)) :
    (processOne W hs st o).node = (Node.onAttestation st.node a).1 := by
  unfold processOne
  rw [h]
  rfl

/-- A delivered object with no canonical event keeps the node state. -/
theorem processOne_node_none (hs : List (Header Info × Nat)) (st : State W)
    (o : ShapeObj pub.n Empty Info Body) (h : W.canonEvent hs o = none) :
    (processOne W hs st o).node = st.node := by
  simp only [processOne, h]

/-! ## Tick duties -/

/-- The node's tick at a public time runs the AC's tick on the node state. -/
theorem nodeTick_node_public (st : State W)
    (h : (params pub hn R.genesisRoot R.δt).IsPublic st.now) :
    (nodeTick W st).node = (Node.acCall st.self st.node st.now .tick).1 := by
  unfold nodeTick
  rw [ite_eq_left h]
  rfl

/-- The node's tick at a time that is not public keeps the node state. -/
theorem nodeTick_node_other (st : State W)
    (h : ¬ (params pub hn R.genesisRoot R.δt).IsPublic st.now) :
    (nodeTick W st).node = st.node := by
  unfold nodeTick
  rw [ite_eq_right h]

/-- The slot proposal runs `ac_proposal` on the node state. -/
theorem propose_node (st : State W) (s : Slot) :
    (propose W st s).1.node = (Node.acProposal st.node st.now).1 := by
  unfold propose
  dsimp only
  split <;> rfl

/-- The FG update is the node's `tickStep .fgUpdate`: `ac_to_fg`, then `attest` at the source it
returns, for any proposer schedule, digest and input, since that step reads none of them. -/
theorem fgUpdate_node (proposer dg) (x : Nat) (st : State W) :
    (fgUpdate W st).node = (Node.tickStep proposer dg st.self st.node st.now x .fgUpdate).1 := by
  unfold fgUpdate Node.tickStep
  simp only
  rcases h : (Node.acToFG st.node st.now).2.2 with _ | C
  · rfl
  · unfold Node.attest
    rcases h' : (Node.acToFG st.node st.now).1.fg.attest (Node.acToFG st.node st.now).1.record
      st.self C with _ | ⟨a, Λ'⟩ <;> simp only [h']

/-! ## Own objects -/

/-- Recording an own block object whose header decodes runs `on_block` on the decoded block. -/
theorem recordOwn_node_block (st : State W) (k : Fin pub.n) (s : Slot) (h : Header Info)
    (cs : List (ShapeObj pub.n Empty Info Body)) (hs : List (Header Info × Nat)) {atts p d}
    (hi : W.decodeInfo h.info = some (atts, p)) (hr : W.rootOf hs h = some d) :
    (recordOwn W st (.mk (.signed k (.proposer s)) (.item h) cs) hs).node =
      (Node.onBlock st.self st.node st.now (W.blockOf d h k atts p)).1 := by
  simp only [recordOwn, hi, hr]
  rfl

end Consensus.Goldilocks.NodeEngine
