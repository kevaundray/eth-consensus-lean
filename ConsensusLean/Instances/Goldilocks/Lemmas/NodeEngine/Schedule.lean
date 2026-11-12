module
public import ConsensusLean.Instances.Goldilocks.Lemmas.NodeEngine.Coverage

public section

/-! # Node engine trace: schedule fields

Three fields of `SimulatesNodeAt` at the canonical trace `simTraceNodeAt` and cut map
`cutMapNode`, as stated there:
* `tick_other`: a tick at a time that is not public writes no record, so its cut interval is
  empty (`simTraceNodeAt_tick_other`);
* `awake_of`: the trace's awake predicate is the run's awake bit within `[0, horizon]`
  (`simTraceNodeAt_awake_of`);
* `awake_to`: every time in the trace's horizon is at most the run's horizon, for a valid run
  (`simTraceNodeAt_awake_to`). A labelled cut carries a record, whose time is the time of its
  event; a valid run's events lie within its horizon. -/

namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {I B : Type} {O : OutputSchema} [DecidableEq I] [Countable I]
  (A : Family I B) (fin : O.Id → Bool)
  (rho : Model.Run (compiled (shapeFamily A fin)) E) (hn : 1 ≤ Fintype.card V) (D : TraceData)

/-! ## `tick_other` -/

/-- **`SimulatesNodeAt.tick_other`.** A tick at a time that is not public has an empty cut
interval. -/
theorem simTraceNodeAt_tick_other : ∀ (v : V) (i : Nat) (t : Time),
    rho.events[i]? = some (.tick v t) →
    ¬ (params (pubOf E) hn (A.runtime (pubOf E) hn).genesisRoot
      (A.runtime (pubOf E) hn).δt).IsPublic t →
      cutMapNode A fin rho hn D (i + 1) = cutMapNode A fin rho hn D i := by
  intro v i t he hp
  exact cutMapNode_succ_of_eventRecords_eq_nil A fin rho hn D
    (eventRecords_tick_of_not_public A fin rho hn D he hp)

/-! ## `awake_of` -/

/-- **`SimulatesNodeAt.awake_of`.** The trace's awake predicate is the run's awake bit within
`[0, horizon]`. -/
theorem simTraceNodeAt_awake_of : ∀ (y : Fin (Fintype.card V)) (t : Time),
    y ∈ honestAt A fin rho t → (simTraceNodeAt A fin rho hn D).awake y t →
      E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon :=
  fun _ _ _ h => h

/-! ## Record times -/

/-- Every record of event `i` carries the time of event `i`: a group's records carry the group's
time, and a delivery's records, over all of its objects, carry the delivery's time. -/
theorem eventRecords_time {i : Nat} {r} (hr : r ∈ eventRecords A fin rho hn D i) :
    ∃ e, rho.events[i]? = some e ∧ r.time = e.time := by
  have hg : ∀ {self st t id e r}, r ∈ group A fin rho hn D self st t id e → r.time = t := by
    intro _ _ _ _ _ _ hr
    obtain ⟨_, -, rfl⟩ := List.mem_mapIdx.mp hr
    rfl
  have hd : ∀ hs self t j os st sub r,
      r ∈ delivery A fin rho hn D hs self t j os st sub → r.time = t := by
    intro hs self t j os
    induction os with
    | nil =>
      intro _ _ _ hr
      exact (List.not_mem_nil hr).elim
    | cons o os ih =>
      intro st sub r hr
      simp only [delivery] at hr
      split at hr
      · rcases List.mem_append.mp hr with h | h
        · exact hg h
        · exact ih _ _ r h
      · exact ih _ _ r hr
  cases he : rho.events[i]? with
  | none =>
    rw [eventRecords_of_getElem?_eq_none A fin rho hn D he] at hr
    exact (List.not_mem_nil hr).elim
  | some e =>
    refine ⟨e, rfl, ?_⟩
    cases e with
    | tick v t =>
      unfold eventRecords at hr
      simp only [he] at hr
      split at hr
      · exact hg hr
      · exact (List.not_mem_nil hr).elim
    | deliver v o t =>
      rw [eventRecords_deliver A fin rho hn D he] at hr
      exact hd _ _ _ _ _ _ _ r hr
    | restart v t =>
      unfold eventRecords at hr
      simp only [he] at hr
      exact hg hr

/-- In a valid run every record's time lies within the run's horizon. -/
theorem mem_records_time (hv : rho.ExecutionValid) {r} (hr : r ∈ records A fin rho hn D) :
    0 ≤ r.time ∧ r.time ≤ rho.horizon := by
  rw [records, List.mem_flatMap] at hr
  obtain ⟨i, -, hri⟩ := hr
  obtain ⟨e, he, ht⟩ := eventRecords_time A fin rho hn D hri
  rw [ht]
  exact hv.in_horizon e (List.mem_of_getElem? he)

/-! ## `awake_to` -/

/-- In a valid run every time in the trace's horizon is at most the run's horizon. -/
theorem simTraceNodeAt_inHorizon_le (hv : rho.ExecutionValid) {t : Time}
    (h : (simTraceNodeAt A fin rho hn D).InHorizon t) : t ≤ rho.horizon := by
  obtain ⟨k, hk, htk⟩ := h
  rcases hk with hl | ⟨T, hT, htT⟩
  · have hlt := (simTraceNodeAt_label_ne_none_iff A fin rho hn D k).mp hl
    rw [simTraceNodeAt_time, List.getElem?_eq_getElem hlt, Option.elim_some] at htk
    exact htk.trans (mem_records_time A fin rho hn D hv (List.getElem_mem hlt)).2
  · have hh : some rho.horizon = some T :=
      (simTraceNodeAt_observationHorizon A fin rho hn D).symm.trans hT
    obtain rfl := Option.some.inj hh
    exact htT

/-- **`SimulatesNodeAt.awake_to`.** In a valid run, an awake time from `0` within the trace's
horizon is awake in the trace. -/
theorem simTraceNodeAt_awake_to (hv : rho.ExecutionValid) : ∀ (y : Fin (Fintype.card V))
    (t : Time), y ∈ honestAt A fin rho t → E.awake (rho.key y) t = true →
    0 ≤ t → (simTraceNodeAt A fin rho hn D).InHorizon t →
      (simTraceNodeAt A fin rho hn D).awake y t := by
  intro y t _ hw ht hh
  exact ⟨hw, ht, simTraceNodeAt_inHorizon_le A fin rho hn D hv hh⟩

end Consensus.Goldilocks.NodeEngine
