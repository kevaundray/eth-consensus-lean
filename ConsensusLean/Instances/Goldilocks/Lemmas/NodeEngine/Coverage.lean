module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Trace

public section

/-! # Node engine trace: cut-map coverage and the finite tail

`cutMapNode i` is the number of records written by the events before event `i`. An event may
write no record (a tick at a non-public time, a delivery whose objects all drop or emit no cut, an
index past the events) or several (a delivery of several objects): nothing here assumes that an
event emits a cut. The labelled cuts of `simTraceNodeAt` are exactly the indices of `records`, so
each lies in the cut interval of an actual event, and they are finite. Past the records the trace
is its constant tail. The tail's `post` default is not related to any engine state. -/

namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {I B : Type} {O : OutputSchema} [DecidableEq I] [Countable I]
  (A : Family I B) (fin : O.Id → Bool)
  (rho : Model.Run (compiled (shapeFamily A fin)) E) (hn : 1 ≤ Fintype.card V) (D : TraceData)

/-! ## The cut map -/

theorem cutMapNode_zero : cutMapNode A fin rho hn D 0 = 0 := by rfl

theorem cutMapNode_succ (i : Nat) :
    cutMapNode A fin rho hn D (i + 1) =
      cutMapNode A fin rho hn D i + (eventRecords A fin rho hn D i).length := by rfl

/-- The cut map counts the records of the events before `i`. -/
theorem cutMapNode_eq_length (i : Nat) :
    cutMapNode A fin rho hn D i =
      ((List.range i).flatMap (eventRecords A fin rho hn D)).length := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [cutMapNode_succ, ih, List.range_succ, List.flatMap_append, List.length_append,
      List.flatMap_singleton]

theorem cutMapNode_mono : Monotone (cutMapNode A fin rho hn D) :=
  monotone_nat_of_le_succ fun i => by
    rw [cutMapNode_succ]
    exact Nat.le_add_right _ _

/-- The terminal value of the cut map is the number of records. -/
theorem cutMapNode_length :
    cutMapNode A fin rho hn D rho.events.length = (records A fin rho hn D).length :=
  cutMapNode_eq_length A fin rho hn D rho.events.length

/-- An event writing no record has an empty cut interval. -/
theorem cutMapNode_succ_of_eventRecords_eq_nil {i : Nat}
    (h : eventRecords A fin rho hn D i = []) :
    cutMapNode A fin rho hn D (i + 1) = cutMapNode A fin rho hn D i := by
  rw [cutMapNode_succ, h, List.length_nil, Nat.add_zero]

/-! ## The records of one event -/

theorem eventRecords_of_getElem?_eq_none {i : Nat} (h : rho.events[i]? = none) :
    eventRecords A fin rho hn D i = [] := by
  unfold eventRecords
  rw [h]

/-- A tick at a time that is not public writes no record. -/
theorem eventRecords_tick_of_not_public {i : Nat} {v : V} {t : Time}
    (h : rho.events[i]? = some (.tick v t))
    (hp : ¬ (params (pubOf E) hn (A.runtime (pubOf E) hn).genesisRoot
      (A.runtime (pubOf E) hn).δt).IsPublic t) :
    eventRecords A fin rho hn D i = [] := by
  unfold eventRecords
  rw [h]
  simp only [hp, ite_false]

/-- A delivery writes the records of all its objects, in order: its whole cut interval. -/
theorem eventRecords_deliver {i : Nat} {v : V} {o} {t : Time}
    (h : rho.events[i]? = some (.deliver v o t)) :
    eventRecords A fin rho hn D i = delivery A fin rho hn D (Model.digests rho.hash o)
      (rho.ownKey v) t i o.parts (engineState A fin rho hn v i).node 0 := by
  unfold eventRecords
  rw [h]

/-! ## The records -/

theorem records_eq_nil_of_events_eq_nil (h : rho.events = []) :
    records A fin rho hn D = [] := by
  rw [← List.length_eq_zero_iff, ← cutMapNode_length, h, List.length_nil, cutMapNode_zero]

/-- The records split at event `i`; the prefix has length `cutMapNode i`
(`cutMapNode_eq_length`). -/
theorem records_eq_append {i : Nat} (hi : i ≤ rho.events.length) :
    records A fin rho hn D = (List.range i).flatMap (eventRecords A fin rho hn D) ++
      (List.range (rho.events.length - i)).flatMap
        (fun j => eventRecords A fin rho hn D (i + j)) := by
  rw [records, ← Nat.add_sub_cancel' hi, List.range_add, List.flatMap_append,
    List.flatMap_map, Nat.add_sub_cancel_left]

/-- Inside the cut interval of event `i`, the records are those of event `i`. -/
theorem records_getElem?_of_mem {i k : Nat} (hi : i < rho.events.length)
    (h1 : cutMapNode A fin rho hn D i ≤ k) (h2 : k < cutMapNode A fin rho hn D (i + 1)) :
    (records A fin rho hn D)[k]? =
      (eventRecords A fin rho hn D i)[k - cutMapNode A fin rho hn D i]? := by
  rw [records_eq_append A fin rho hn D (Nat.succ_le_of_lt hi), List.getElem?_append_left
    (by rwa [← cutMapNode_eq_length]), List.range_succ, List.flatMap_append,
    List.flatMap_singleton, List.getElem?_append_right (by rwa [← cutMapNode_eq_length]),
    ← cutMapNode_eq_length]

/-! ## The canonical trace -/

theorem simTraceNodeAt_label (k : Nat) :
    (simTraceNodeAt A fin rho hn D).label k = (records A fin rho hn D)[k]?.map Record.label := by
  rfl

theorem simTraceNodeAt_time (k : Nat) :
    (simTraceNodeAt A fin rho hn D).time k =
      (records A fin rho hn D)[k]?.elim (rho.horizon + 1) Record.time := by
  rfl

theorem simTraceNodeAt_post (k : Nat) :
    (simTraceNodeAt A fin rho hn D).post k =
      (records A fin rho hn D)[k]?.elim (Node.init _) Record.post := by
  rfl

theorem simTraceNodeAt_observationHorizon :
    (simTraceNodeAt A fin rho hn D).observationHorizon = some rho.horizon := by
  rfl

/-- The labelled cuts are exactly the indices of the records. -/
theorem simTraceNodeAt_label_ne_none_iff (k : Nat) :
    (simTraceNodeAt A fin rho hn D).label k ≠ none ↔ k < (records A fin rho hn D).length := by
  rw [simTraceNodeAt_label, Ne, Option.map_eq_none_iff, List.getElem?_eq_none_iff, not_le]

/-- Every labelled cut lies in the cut interval of an actual event. -/
theorem simTraceNodeAt_covered (k : Nat) (hk : (simTraceNodeAt A fin rho hn D).label k ≠ none) :
    ∃ i < rho.events.length,
      cutMapNode A fin rho hn D i ≤ k ∧ k < cutMapNode A fin rho hn D (i + 1) := by
  rw [simTraceNodeAt_label_ne_none_iff, ← cutMapNode_length] at hk
  generalize rho.events.length = n at hk ⊢
  induction n with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    by_cases h : k < cutMapNode A fin rho hn D n
    · obtain ⟨i, hi, hik⟩ := ih h
      exact ⟨i, Nat.lt_succ_of_lt hi, hik⟩
    · exact ⟨n, Nat.lt_succ_self n, Nat.le_of_not_lt h, hk⟩

/-- A labelled cut carries the record at its position in its event's records. -/
theorem simTraceNodeAt_label_of_mem {i k : Nat} (hi : i < rho.events.length)
    (h1 : cutMapNode A fin rho hn D i ≤ k) (h2 : k < cutMapNode A fin rho hn D (i + 1)) :
    (simTraceNodeAt A fin rho hn D).label k =
      (eventRecords A fin rho hn D i)[k - cutMapNode A fin rho hn D i]?.map Record.label := by
  rw [simTraceNodeAt_label, records_getElem?_of_mem A fin rho hn D hi h1 h2]

/-! ## The finite tail -/

section Tail
variable {A fin rho hn D} {k : Nat} (hk : (records A fin rho hn D).length ≤ k)
include hk

theorem simTraceNodeAt_label_of_length_le : (simTraceNodeAt A fin rho hn D).label k = none := by
  rw [simTraceNodeAt_label, List.getElem?_eq_none hk, Option.map_none]

theorem simTraceNodeAt_time_of_length_le :
    (simTraceNodeAt A fin rho hn D).time k = rho.horizon + 1 := by
  rw [simTraceNodeAt_time, List.getElem?_eq_none hk, Option.elim_none]

theorem simTraceNodeAt_post_of_length_le :
    (simTraceNodeAt A fin rho hn D).post k = Node.init _ := by
  rw [simTraceNodeAt_post, List.getElem?_eq_none hk, Option.elim_none]

end Tail

theorem simTraceNodeAt_label_of_events_eq_nil (h : rho.events = []) (k : Nat) :
    (simTraceNodeAt A fin rho hn D).label k = none :=
  simTraceNodeAt_label_of_length_le (by
    rw [records_eq_nil_of_events_eq_nil A fin rho hn D h, List.length_nil]
    exact Nat.zero_le k)

/-! ## Finiteness -/

theorem simTraceNodeAt_labelled_finite :
    {k | (simTraceNodeAt A fin rho hn D).label k ≠ none}.Finite :=
  (Set.finite_lt_nat (records A fin rho hn D).length).subset
    fun k hk => (simTraceNodeAt_label_ne_none_iff A fin rho hn D k).mp hk

/-- The `finite` field of `Growing.LocalRun`: finitely many labelled cuts in every bounded
interval. -/
theorem simTraceNodeAt_finite : ∀ T : Time,
    {i | (simTraceNodeAt A fin rho hn D).label i ≠ none ∧
      (simTraceNodeAt A fin rho hn D).time i ≤ T}.Finite :=
  fun _ => (simTraceNodeAt_labelled_finite A fin rho hn D).subset fun _ hk => hk.1

end Consensus.Goldilocks.NodeEngine
