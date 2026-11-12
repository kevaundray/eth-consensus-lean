module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Engine

public section

/-! # Node engine handlers: installing and keeping the node state

The engine handlers that install a node state or keep it (`State.node`):
* `apply` installs the node state of its handler result (`apply_node`);
* the clock handler only sets the clock (`nodeShape_clock`, `nodeShape_clock_node`);
* the batch poll's node state is the FG update's when the FG update is due, and the node state
  before it otherwise (`pollBatch_node`, `pollBatch_node_of_fgDue`,
  `pollBatch_node_of_not_fgDue`);
* recording an own object keeps the node state, unless it is a proposer-signed header whose
  info decodes and whose root is found (`recordOwn_node_of_not_block`,
  `recordOwn_node_unsigned_data`, `recordOwn_node_decode_none`, `recordOwn_node_root_none`;
  that remaining case is `recordOwn_node_block` in `Handlers`). -/

namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape
open Consensus.Model (Public)

variable {pub : Public} {hn : 1 ≤ pub.n} {S M Q Info Body : Type}
  [DecidableEq Info] [Countable Info] {R : Runtime pub hn S M Q} (W : Wire R Info Body)

/-- `apply` installs the node state of its handler result. -/
theorem apply_node (st : State W) r : (apply W st r).node = r.1 := rfl

/-- The clock handler sets the clock and nothing else. -/
theorem nodeShape_clock {Out : Type} (isFinalized : Out → Bool) (st : State W) (t : Time) :
    ((nodeShape W isFinalized).clock st t : State W) = { st with now := t } := rfl

/-- The clock handler keeps the node state. -/
theorem nodeShape_clock_node {Out : Type} (isFinalized : Out → Bool) (st : State W) (t : Time) :
    ((nodeShape W isFinalized).clock st t : State W).node = st.node := rfl

/-- The batch poll's node state: the FG update's when it is due, the node state otherwise. -/
theorem pollBatch_node (st : State W) (t : Time) :
    (pollBatch W st t).1.node = (if st.fgDue then fgUpdate W st else st).node := rfl

/-- When the FG update is due, the batch poll's node state is the FG update's. -/
theorem pollBatch_node_of_fgDue (st : State W) (t : Time) (h : st.fgDue = true) :
    (pollBatch W st t).1.node = (fgUpdate W st).node := by
  rw [pollBatch_node, ite_eq_left h]

/-- When the FG update is not due, the batch poll keeps the node state. -/
theorem pollBatch_node_of_not_fgDue (st : State W) (t : Time) (h : st.fgDue = false) :
    (pollBatch W st t).1.node = st.node := by
  have hc : ¬ st.fgDue = true := by simp [h]
  rw [pollBatch_node, ite_eq_right hc]

/-- Recording an own object that is not a proposer-signed header keeps the node state. -/
theorem recordOwn_node_of_not_block (st : State W) (o : ShapeObj pub.n Empty Info Body)
    (hs : List (Header Info × Nat))
    (hob : ∀ k s h cs, o ≠ .mk (.signed k (.proposer s)) (.item h) cs) :
    (recordOwn W st o hs).node = st.node := by
  unfold recordOwn
  split
  · split <;> rfl
  · exact (hob _ _ _ _ rfl).elim
  · rfl

/-- Recording an own unsigned data object, the relay body or another, keeps the node state. -/
theorem recordOwn_node_unsigned_data (st : State W) (b : Body)
    (cs : List (ShapeObj pub.n Empty Info Body)) (hs : List (Header Info × Nat)) :
    (recordOwn W st (.mk .none (.data b) cs) hs).node = st.node :=
  recordOwn_node_of_not_block W st (.mk .none (.data b) cs) hs fun _ _ _ _ h => by cases h

/-- Recording an own proposer-signed header whose info does not decode keeps the node state. -/
theorem recordOwn_node_decode_none (st : State W) (k : Fin pub.n) (s : Slot) (h : Header Info)
    (cs : List (ShapeObj pub.n Empty Info Body)) (hs : List (Header Info × Nat))
    (hi : W.decodeInfo h.info = none) :
    (recordOwn W st (.mk (.signed k (.proposer s)) (.item h) cs) hs).node = st.node := by
  cases hr : W.rootOf hs h <;> simp only [recordOwn, hi, hr]

/-- Recording an own proposer-signed header whose root is not found keeps the node state. -/
theorem recordOwn_node_root_none (st : State W) (k : Fin pub.n) (s : Slot) (h : Header Info)
    (cs : List (ShapeObj pub.n Empty Info Body)) (hs : List (Header Info × Nat))
    (hr : W.rootOf hs h = none) :
    (recordOwn W st (.mk (.signed k (.proposer s)) (.item h) cs) hs).node = st.node := by
  cases hi : W.decodeInfo h.info with
  | none => simp only [recordOwn, hi, hr]
  | some ap =>
    rcases ap with ⟨atts, p⟩
    simp only [recordOwn, hi, hr]

end Consensus.Goldilocks.NodeEngine
