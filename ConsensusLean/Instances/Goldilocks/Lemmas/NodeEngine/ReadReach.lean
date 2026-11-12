module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.NodeEngine.Simulation
public import ConsensusLean.Instances.Goldilocks.Lemmas.NodeEngine.Clock
public import ConsensusLean.Instances.Goldilocks.Lemmas.NodeEngine.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.NodeEngine.HandlersKeep

public section

/-! # Node engine: the read and FG-reachability exports

Two exports of `Statements/NodeEngine/Simulation` hold for every family, with their premises
unused:
* `ReadExport` (`readExport`): the chain trace reads the engine output `outOf` of the engine
  state, by the definitions of `chainTrace`, the family's `out` and `nodeShape.out`;
* `FGReachExport` (`fgReachExport`): every node's FG store is reachable from the initial store.
  The node's initial store is `Store.init` of the genesis payload. The AC calls (`acCall`,
  `acProposal`, `acToFG`, a restart) keep the store; an accepted `on_block` and an
  `on_attestation` (from the wire or from `attest` in the FG update) are one `Store.Step` each.
  Every engine handler is made of these, so every engine state of every node, honest or not, has a
  reachable store. -/

namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape
open Consensus.Model (Public pubOf)

/-! ## Node handlers -/

section Node

variable {P : Params} {N : NodeAC P}

/-- `on_block` keeps the store or makes one store step, the accepted block. -/
theorem node_onBlock_fgReach {acp₀ : N.Payload} (self : Fin P.n) (st : NodeState N) (t : Time)
    (B : N.Blk) (h : st.fg.Reachable acp₀) : (Node.onBlock self st t B).1.fg.Reachable acp₀ := by
  unfold Node.onBlock
  split
  · exact h
  · cases hb : st.fg.onBlock B with
    | none => exact h
    | some fg' => exact Relation.ReflTransGen.tail h (Or.inl ⟨B, hb⟩)

end Node

/-! ## Engine handlers -/

section Handlers

variable {pub : Public} {hn : 1 ≤ pub.n} {S M Q Info Body : Type}
  [DecidableEq Info] [Countable Info] {R : Runtime pub hn S M Q} (W : Wire R Info Body)

/-- The initial engine state's store is the initial store. -/
theorem nodeShape_init_fgReach {Out : Type} (isFinalized : Out → Bool) (k : Fin pub.n)
    (p : ShapeRole (nodeShape W isFinalized).skel.Kind → Bool) :
    ((nodeShape W isFinalized).init k p : State W).node.fg.Reachable
      R.operations.toAC.genesisPayload :=
  Relation.ReflTransGen.refl

/-- Processing one delivered object keeps a reachable store reachable. -/
theorem processOne_fgReach {acp₀} (hs : List (Header Info × Nat)) (st : State W)
    (o : ShapeObj pub.n Empty Info Body) (h : st.node.fg.Reachable acp₀) :
    (processOne W hs st o).node.fg.Reachable acp₀ := by
  unfold processOne
  split <;> (try dsimp only) <;> (try split) <;>
    first
      | exact h
      | exact Relation.ReflTransGen.tail h (Or.inr ⟨_, rfl⟩)
      | exact node_onBlock_fgReach _ _ _ _ h

/-- Processing a list of delivered objects keeps a reachable store reachable. -/
theorem foldl_processOne_fgReach {acp₀} (hs : List (Header Info × Nat))
    (os : List (ShapeObj pub.n Empty Info Body)) :
    ∀ st : State W, st.node.fg.Reachable acp₀ →
      (os.foldl (processOne W hs) st).node.fg.Reachable acp₀ := by
  induction os with
  | nil => exact fun _ h => h
  | cons o os ih => exact fun st h => ih _ (processOne_fgReach W hs st o h)

/-- A delivery's `process` keeps a reachable store reachable. -/
theorem process_fgReach {acp₀} (st : State W) (o : ShapeObj pub.n Empty Info Body)
    (hs : List (Header Info × Nat)) (h : st.node.fg.Reachable acp₀) :
    (process W st o hs).node.fg.Reachable acp₀ :=
  foldl_processOne_fgReach W hs o.parts st h

/-- Recording an own object keeps a reachable store reachable. -/
theorem recordOwn_fgReach {acp₀} (st : State W) (o : ShapeObj pub.n Empty Info Body)
    (hs : List (Header Info × Nat)) (h : st.node.fg.Reachable acp₀) :
    (recordOwn W st o hs).node.fg.Reachable acp₀ := by
  by_cases hb : ∃ k s hd cs, o = .mk (.signed k (.proposer s)) (.item hd) cs
  · obtain ⟨k, s, hd, cs, rfl⟩ := hb
    cases hi : W.decodeInfo hd.info with
    | none =>
      rw [recordOwn_node_decode_none W st k s hd cs hs hi]
      exact h
    | some ap =>
      rcases ap with ⟨atts, p⟩
      cases hr : W.rootOf hs hd with
      | none =>
        rw [recordOwn_node_root_none W st k s hd cs hs hr]
        exact h
      | some d =>
        rw [recordOwn_node_block W st k s hd cs hs hi hr]
        exact node_onBlock_fgReach _ _ _ _ h
  · rw [recordOwn_node_of_not_block W st o hs fun k s hd cs he => hb ⟨k, s, hd, cs, he⟩]
    exact h

/-- The node's tick keeps the store. -/
theorem nodeTick_fgReach {acp₀} (st : State W) (h : st.node.fg.Reachable acp₀) :
    (nodeTick W st).node.fg.Reachable acp₀ := by
  by_cases hp : (params pub hn R.genesisRoot R.δt).IsPublic st.now
  · rw [nodeTick_node_public W st hp]
    exact h
  · rw [nodeTick_node_other W st hp]
    exact h

/-- The slot proposal keeps the store. -/
theorem propose_fgReach {acp₀} (st : State W) (s : Slot) (h : st.node.fg.Reachable acp₀) :
    (propose W st s).1.node.fg.Reachable acp₀ := by
  rw [propose_node]
  exact h

/-- The FG update keeps the store or processes its own attestation, one store step. -/
theorem fgUpdate_fgReach {acp₀} (st : State W) (h : st.node.fg.Reachable acp₀) :
    (fgUpdate W st).node.fg.Reachable acp₀ := by
  unfold fgUpdate
  simp only
  rcases h1 : (Node.acToFG st.node st.now).2.2 with _ | C
  · exact h
  · dsimp only
    rcases h2 : (Node.acToFG st.node st.now).1.fg.attest (Node.acToFG st.node st.now).1.record
      st.self C with _ | ⟨a, Λ'⟩
    · exact h
    · exact Relation.ReflTransGen.tail h (Or.inr ⟨a, rfl⟩)

/-- The batch poll keeps a reachable store reachable. -/
theorem pollBatch_fgReach {acp₀} (st : State W) (t : Time) (h : st.node.fg.Reachable acp₀) :
    (pollBatch W st t).1.node.fg.Reachable acp₀ := by
  rw [pollBatch_node]
  split
  · exact fgUpdate_fgReach W st h
  · exact h

/-- A restart keeps the store. -/
theorem restore_fgReach {acp₀} (k : Fin pub.n) (st : State W) (t : Time)
    (h : st.node.fg.Reachable acp₀) : (restore W k st t).node.fg.Reachable acp₀ :=
  h

end Handlers

/-! ## The compiled shape -/

variable {V : Type} [Fintype V] {E : Env V}
  {I B : Type} {O : OutputSchema} [DecidableEq I] [Countable I]
  (A : Family I B) (fin : O.Id → Bool)
  (rho : Model.Run (compiled (shapeFamily A fin)) E) (hn : 1 ≤ Fintype.card V)

/-- The compiled initial state's store is the initial store. -/
theorem compiled_init_fgReach (k : Fin (Fintype.card V))
    (p : (Model.protoOf (compiled (shapeFamily A fin)) E).Role → Bool) :
    (((Model.protoOf (compiled (shapeFamily A fin)) E).init k p).1 hn).node.fg.Reachable
      (nodeAC (E := E) A hn).genesisPayload :=
  Relation.ReflTransGen.refl

/-- The compiled clock keeps the store. -/
theorem compiled_clock_fgReach (s : (Model.protoOf (compiled (shapeFamily A fin)) E).State)
    (t : Time) xs (h : (s.1 hn).node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload) :
    (((Model.protoOf (compiled (shapeFamily A fin)) E).clock s t xs).1 hn).node.fg.Reachable
      (nodeAC (E := E) A hn).genesisPayload :=
  h

/-- The compiled restore keeps the store of the durable state. -/
theorem compiled_restore_fgReach (k : Fin (Fintype.card V))
    (p : (Model.protoOf (compiled (shapeFamily A fin)) E).Role → Bool)
    (d : (Model.protoOf (compiled (shapeFamily A fin)) E).Durable) (t : Time)
    (h : (d hn).node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload) :
    (((Model.protoOf (compiled (shapeFamily A fin)) E).restore k p d t).1 hn).node.fg.Reachable
      (nodeAC (E := E) A hn).genesisPayload :=
  restore_fgReach (A.wire (pubOf E) hn) k (d hn) t h

/-- The compiled `process` keeps a reachable store reachable. -/
theorem compiled_process_fgReach (s : (Model.protoOf (compiled (shapeFamily A fin)) E).State)
    (o : (Model.protoOf (compiled (shapeFamily A fin)) E).Object)
    (hs : List ((Model.protoOf (compiled (shapeFamily A fin)) E).Item × Nat))
    (h : (s.1 hn).node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload) :
    (((Model.protoOf (compiled (shapeFamily A fin)) E).process s o hs).1 hn).node.fg.Reachable
      (nodeAC (E := E) A hn).genesisPayload :=
  process_fgReach (A.wire (pubOf E) hn) (s.1 hn) o hs h

/-- The compiled `recordOwn` keeps a reachable store reachable. -/
theorem compiled_recordOwn_fgReach (s : (Model.protoOf (compiled (shapeFamily A fin)) E).State)
    (o : (Model.protoOf (compiled (shapeFamily A fin)) E).Object)
    (hs : List ((Model.protoOf (compiled (shapeFamily A fin)) E).Item × Nat))
    (h : (s.1 hn).node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload) :
    (((Model.protoOf (compiled (shapeFamily A fin)) E).recordOwn s o hs).1 hn).node.fg.Reachable
      (nodeAC (E := E) A hn).genesisPayload :=
  recordOwn_fgReach (A.wire (pubOf E) hn) (s.1 hn) o hs h

/-- Every compiled duty keeps a reachable store reachable. -/
theorem compiled_act_fgReach (s : (Model.protoOf (compiled (shapeFamily A fin)) E).State)
    (d : (Model.protoOf (compiled (shapeFamily A fin)) E).Duty)
    (h : (s.1 hn).node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload) :
    ((((Model.protoOf (compiled (shapeFamily A fin)) E).act s d).1.1 hn).node.fg).Reachable
      (nodeAC (E := E) A hn).genesisPayload := by
  cases d with
  | propose slot hs =>
    have hp := propose_fgReach (A.wire (pubOf E) hn) (s.1 hn) slot h
    rw [← compiled_act_propose A fin hn s slot hs] at hp
    exact hp
  | act _ k => exact k.elim
  | pollPropose t =>
    have hp := nodeTick_fgReach (A.wire (pubOf E) hn) (s.1 hn) h
    rw [← compiled_act_pollPropose A fin hn s t] at hp
    exact hp
  | poll t =>
    have hp := pollBatch_fgReach (A.wire (pubOf E) hn) (s.1 hn) t h
    rw [← compiled_act_poll A fin hn s t] at hp
    exact hp

/-! ## Engine steps of one node -/

/-- An engine tick keeps a reachable store reachable. -/
theorem run_tick_fgReach (nd : Model.Node (Model.protoOf (compiled (shapeFamily A fin)) E))
    (v : V) (t : Time)
    (h : (nd.st.1 hn).node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload) :
    ((rho.tick nd v t).1.st.1 hn).node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload := by
  refine rho.tick_invariant
    (fun s => (s.1 hn).node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload) nd v t ?_ ?_ ?_
  · intro s d _ hs
    exact compiled_act_fgReach A fin hn s d hs
  · intro s o hs' _ hs
    exact compiled_recordOwn_fgReach A fin hn s o hs' hs
  · exact compiled_clock_fgReach A fin hn nd.st t _ h

/-- An engine delivery keeps a reachable store reachable. -/
theorem run_deliver_fgReach (nd : Model.Node (Model.protoOf (compiled (shapeFamily A fin)) E))
    (v : V) (o : (Model.protoOf (compiled (shapeFamily A fin)) E).Object) (t : Time)
    (h : (nd.st.1 hn).node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload) :
    ((rho.deliver nd v o t).1.st.1 hn).node.fg.Reachable
      (nodeAC (E := E) A hn).genesisPayload := by
  refine rho.deliver_invariant
    (fun s => (s.1 hn).node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload) nd v o t
    ?_ ?_ ?_
  · intro s d _ hs
    exact compiled_act_fgReach A fin hn s d hs
  · intro s o' hs' _ hs
    exact compiled_recordOwn_fgReach A fin hn s o' hs' hs
  · exact compiled_process_fgReach A fin hn nd.st o _ h

/-! ## Every engine state -/

variable [DecidableEq V]

private theorem stateBefore_succ_none_fg {i : Nat} (he : rho.events[i]? = none) :
    rho.stateBefore (i + 1) = rho.stateBefore i := by
  simp [Model.Run.stateBefore, List.take_add_one, he]

/-- Every node's store before every event is reachable, with no honesty or validity premise. -/
theorem stateBefore_fgReach (i : Nat) : ∀ v : V,
    ((rho.stateBefore i v).st.1 hn).node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload := by
  induction i with
  | zero =>
    intro v
    exact compiled_init_fgReach A fin hn (rho.ownKey v) _
  | succ i ih =>
    intro v
    cases he : rho.events[i]? with
    | none =>
      rw [stateBefore_succ_none_fg A fin rho he]
      exact ih v
    | some e =>
      rw [rho.stateBefore_succ he]
      cases e with
      | tick w t =>
        simp only [Model.Run.step, Function.update_apply]
        split
        · exact run_tick_fgReach A fin rho hn _ w t (ih w)
        · exact ih v
      | deliver w o t =>
        simp only [Model.Run.step, Function.update_apply]
        split
        · exact run_deliver_fgReach A fin rho hn _ w o t (ih w)
        · exact ih v
      | restart w t =>
        simp only [Model.Run.step, Function.update_apply]
        split
        · exact compiled_restore_fgReach A fin hn _ _ _ t (ih w)
        · exact ih v

/-! ## The exports -/

/-- **`FGReachExport`.** Every node's FG store before every event cut is reachable. -/
theorem fgReachExport : FGReachExport A fin rho hn := by
  intro _ v i _ _
  exact stateBefore_fgReach A fin rho hn i v

/-- The chain trace reads the engine output of the engine state. -/
theorem read_eq_outOf (g : O.Id) (v : V) (i : Nat) :
    (chainTrace rho).read g v i =
      outOf (runWire (E := E) A hn) (engineState A fin rho hn v i) (fin g) := by
  change (shapeFamily A fin (pubOf E)).out g (rho.stateBefore i v).st.1 = _
  simp only [shapeFamily, dite_eq_left hn]
  rfl

/-- **`ReadExport`.** -/
theorem readExport : ReadExport A fin rho hn := by
  intro _ v i g _
  exact read_eq_outOf A fin rho hn g v i

end Consensus.Goldilocks.NodeEngine
