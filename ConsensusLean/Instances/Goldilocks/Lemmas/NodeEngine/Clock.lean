module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Trace
public import ConsensusLean.Lemmas.Model.Candidates
public import ConsensusLean.Lemmas.Model.Objects

public section

/-! # Node engine: the stored clock

The engine state stores a clock `now`. Only three handlers write it: `init` sets `0`, `clock` sets
the tick time at every tick, and `restore` sets the restart time at a restart. Every other handler
of the compiled shape keeps it: the duty handlers (`propose`, `pollPropose` as `nodeTick`, `poll`
as `pollBatch` with its FG update), `process` of every object of a delivery, and `recordOwn` of
every released duty or gossip object. The engine's `stateBefore` folds the events of all nodes,
so for every node `v`, honest or faulty, the stored clock before event `i` is the time of `v`'s
last tick or restart before `i`, and `0` if it has none (`engineState_now`). Deliveries keep the
clock. Events of other nodes, and indices past the events, change nothing.

This is the actual stored clock of the engine state, not the time at which it is read. -/

namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape
open Consensus.Model (Public pubOf)

/-! ## Engine handlers -/

section Handlers

variable {pub : Public} {hn : 1 ≤ pub.n} {S M Q Info Body : Type}
  [DecidableEq Info] [Countable Info] {R : Runtime pub hn S M Q} (W : Wire R Info Body)

/-- The initial engine state's clock is `0`. -/
theorem nodeShape_init_now {Out : Type} (isFinalized : Out → Bool) (k : Fin pub.n)
    (p : ShapeRole (nodeShape W isFinalized).skel.Kind → Bool) :
    ((nodeShape W isFinalized).init k p : State W).now = 0 := rfl

/-- The clock handler sets the clock to the tick time. -/
theorem nodeShape_clock_now {Out : Type} (isFinalized : Out → Bool) (st : State W) (t : Time) :
    ((nodeShape W isFinalized).clock st t : State W).now = t := rfl

/-- A restart sets the clock to the restart time. -/
theorem restore_now (k : Fin pub.n) (st : State W) (t : Time) :
    (restore W k st t).now = t := rfl

/-- Applying a handler result keeps the clock. -/
theorem apply_now (st : State W) r : (apply W st r).now = st.now := rfl

/-- Processing one delivered object keeps the clock. -/
theorem processOne_now (hs : List (Header Info × Nat)) (st : State W)
    (o : ShapeObj pub.n Empty Info Body) : (processOne W hs st o).now = st.now := by
  unfold processOne
  split <;> (try dsimp only) <;> (try split) <;> rfl

/-- Processing a list of delivered objects keeps the clock. -/
theorem foldl_processOne_now (hs : List (Header Info × Nat))
    (os : List (ShapeObj pub.n Empty Info Body)) (st : State W) :
    (os.foldl (processOne W hs) st).now = st.now := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih => rw [List.foldl_cons, ih, processOne_now]

/-- A delivery's `process`, over all of its objects, keeps the clock. -/
theorem process_now (st : State W) (o : ShapeObj pub.n Empty Info Body)
    (hs : List (Header Info × Nat)) : (process W st o hs).now = st.now :=
  foldl_processOne_now W hs o.parts st

/-- Recording an own released object keeps the clock. -/
theorem recordOwn_now (st : State W) (o : ShapeObj pub.n Empty Info Body)
    (hs : List (Header Info × Nat)) : (recordOwn W st o hs).now = st.now := by
  unfold recordOwn
  split <;> (try split) <;> rfl

/-- The node's tick (the `pollPropose` duty) keeps the clock. -/
theorem nodeTick_now (st : State W) : (nodeTick W st).now = st.now := by
  unfold nodeTick
  split <;> rfl

/-- The slot proposal keeps the clock. -/
theorem propose_now (st : State W) (s : Slot) : (propose W st s).1.now = st.now := by
  unfold propose
  dsimp only
  split <;> rfl

/-- The FG update keeps the clock. -/
theorem fgUpdate_now (st : State W) : (fgUpdate W st).now = st.now := by
  unfold fgUpdate
  simp only
  split
  · rfl
  · split <;> rfl

/-- The batch poll (the `poll` duty), with its FG update when due, keeps the clock. -/
theorem pollBatch_now (st : State W) (t : Time) : (pollBatch W st t).1.now = st.now := by
  unfold pollBatch
  simp only
  split <;> first | exact fgUpdate_now W st | rfl

end Handlers

/-! ## The compiled shape -/

variable {V : Type} [Fintype V] {E : Env V}
  {I B : Type} {O : OutputSchema} [DecidableEq I] [Countable I]
  (A : Family I B) (fin : O.Id → Bool)
  (rho : Model.Run (compiled (shapeFamily A fin)) E) (hn : 1 ≤ Fintype.card V)

/-- The compiled initial state's clock is `0`. -/
theorem compiled_init_now (k : Fin (Fintype.card V))
    (p : (Model.protoOf (compiled (shapeFamily A fin)) E).Role → Bool) :
    (((Model.protoOf (compiled (shapeFamily A fin)) E).init k p).1 hn).now = 0 := rfl

/-- The compiled clock sets the clock to the tick time. -/
theorem compiled_clock_now (s : (Model.protoOf (compiled (shapeFamily A fin)) E).State)
    (t : Time) xs :
    (((Model.protoOf (compiled (shapeFamily A fin)) E).clock s t xs).1 hn).now = t := rfl

/-- The compiled restore sets the clock to the restart time. -/
theorem compiled_restore_now (k : Fin (Fintype.card V))
    (p : (Model.protoOf (compiled (shapeFamily A fin)) E).Role → Bool)
    (d : (Model.protoOf (compiled (shapeFamily A fin)) E).Durable) (t : Time) :
    (((Model.protoOf (compiled (shapeFamily A fin)) E).restore k p d t).1 hn).now = t := rfl

/-- The compiled `process` keeps the clock. -/
theorem compiled_process_now (s : (Model.protoOf (compiled (shapeFamily A fin)) E).State)
    (o : (Model.protoOf (compiled (shapeFamily A fin)) E).Object)
    (hs : List ((Model.protoOf (compiled (shapeFamily A fin)) E).Item × Nat)) :
    (((Model.protoOf (compiled (shapeFamily A fin)) E).process s o hs).1 hn).now =
      (s.1 hn).now :=
  process_now (A.wire (pubOf E) hn) (s.1 hn) o hs

/-- The compiled `recordOwn` keeps the clock. -/
theorem compiled_recordOwn_now (s : (Model.protoOf (compiled (shapeFamily A fin)) E).State)
    (o : (Model.protoOf (compiled (shapeFamily A fin)) E).Object)
    (hs : List ((Model.protoOf (compiled (shapeFamily A fin)) E).Item × Nat)) :
    (((Model.protoOf (compiled (shapeFamily A fin)) E).recordOwn s o hs).1 hn).now =
      (s.1 hn).now :=
  recordOwn_now (A.wire (pubOf E) hn) (s.1 hn) o hs

/-- The compiled `propose` duty is the engine's slot proposal. -/
theorem compiled_act_propose (s : (Model.protoOf (compiled (shapeFamily A fin)) E).State)
    (slot : Slot) (h : 0 < slot) :
    ((Model.protoOf (compiled (shapeFamily A fin)) E).act s (.propose slot h)).1.1 hn =
      (propose (A.wire (pubOf E) hn) (s.1 hn) slot).1 := by
  change ((shapeFamily A fin (pubOf E)).propose s.1 slot).1 hn = _
  simp only [shapeFamily, dite_eq_left hn]
  rfl

/-- The compiled `pollPropose` duty is the engine's node tick. -/
theorem compiled_act_pollPropose (s : (Model.protoOf (compiled (shapeFamily A fin)) E).State)
    (t : Nat) :
    ((Model.protoOf (compiled (shapeFamily A fin)) E).act s (.pollPropose t)).1.1 hn =
      nodeTick (A.wire (pubOf E) hn) (s.1 hn) := by
  change ((shapeFamily A fin (pubOf E)).pollPropose s.1 t).1 hn = _
  simp only [shapeFamily, dite_eq_left hn]
  rfl

/-- The compiled `poll` duty is the engine's batch poll. -/
theorem compiled_act_poll (s : (Model.protoOf (compiled (shapeFamily A fin)) E).State)
    (t : Nat) :
    ((Model.protoOf (compiled (shapeFamily A fin)) E).act s (.poll t)).1.1 hn =
      (pollBatch (A.wire (pubOf E) hn) (s.1 hn) t).1 := by
  change ((shapeFamily A fin (pubOf E)).pollBatch s.1 t).1 hn = _
  simp only [shapeFamily, dite_eq_left hn]
  rfl

/-- Every compiled duty keeps the clock; the committee duty has no kind to run. -/
theorem compiled_act_now (s : (Model.protoOf (compiled (shapeFamily A fin)) E).State)
    (d : (Model.protoOf (compiled (shapeFamily A fin)) E).Duty) :
    (((Model.protoOf (compiled (shapeFamily A fin)) E).act s d).1.1 hn).now =
      (s.1 hn).now := by
  cases d with
  | propose slot h =>
    have hp := propose_now (A.wire (pubOf E) hn) (s.1 hn) slot
    rw [← compiled_act_propose A fin hn s slot h] at hp
    exact hp
  | act _ k => exact k.elim
  | pollPropose t =>
    have hp := nodeTick_now (A.wire (pubOf E) hn) (s.1 hn)
    rw [← compiled_act_pollPropose A fin hn s t] at hp
    exact hp
  | poll t =>
    have hp := pollBatch_now (A.wire (pubOf E) hn) (s.1 hn) t
    rw [← compiled_act_poll A fin hn s t] at hp
    exact hp

/-! ## Engine steps of one node -/

/-- A release round, including the gossip of a tick or delivery, keeps the clock. -/
theorem releaseAll_now (hash : (Model.protoOf (compiled (shapeFamily A fin)) E).Item → Nat)
    (k : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (shapeFamily A fin)) E))
    (cs : List (Model.protoOf (compiled (shapeFamily A fin)) E).Object) :
    ((Model.releaseAll (Model.protoOf (compiled (shapeFamily A fin)) E) hash k nd cs).1.st.1
      hn).now = (nd.st.1 hn).now :=
  Model.releaseAll_invariant (P := Model.protoOf (compiled (shapeFamily A fin)) E)
    (fun s => (s.1 hn).now = (nd.st.1 hn).now) hash k nd cs
    (fun s o hs _ h => (compiled_recordOwn_now A fin hn s o hs).trans h) rfl

/-- Running duties, each with its release round, keeps the clock. -/
theorem runDuties_now (v : V)
    (nd : Model.Node (Model.protoOf (compiled (shapeFamily A fin)) E))
    (ds : List (Model.protoOf (compiled (shapeFamily A fin)) E).Duty) :
    ((rho.runDuties v nd ds).1.st.1 hn).now = (nd.st.1 hn).now :=
  rho.runDuties_invariant (fun s => (s.1 hn).now = (nd.st.1 hn).now) v ds nd
    (fun s d _ h => (compiled_act_now A fin hn s d).trans h)
    (fun s o hs _ h => (compiled_recordOwn_now A fin hn s o hs).trans h) rfl

/-- After an engine tick at `t`, awake or not, the clock is `t`: the clock handler sets it, and
the duties and the gossip keep it. -/
theorem run_tick_now (nd : Model.Node (Model.protoOf (compiled (shapeFamily A fin)) E))
    (v : V) (t : Time) : ((rho.tick nd v t).1.st.1 hn).now = t := by
  refine rho.tick_invariant (fun s => (s.1 hn).now = t) nd v t ?_ ?_ ?_
  · intro s d _ h
    exact (compiled_act_now A fin hn s d).trans h
  · intro s o hs _ h
    exact (compiled_recordOwn_now A fin hn s o hs).trans h
  · exact compiled_clock_now A fin hn nd.st t _

/-- An engine delivery keeps the clock: `process` of every delivered object, the delivery duties
and the gossip all keep it. -/
theorem run_deliver_now (nd : Model.Node (Model.protoOf (compiled (shapeFamily A fin)) E))
    (v : V) (o : (Model.protoOf (compiled (shapeFamily A fin)) E).Object) (t : Time) :
    ((rho.deliver nd v o t).1.st.1 hn).now = (nd.st.1 hn).now := by
  refine rho.deliver_invariant (fun s => (s.1 hn).now = (nd.st.1 hn).now) nd v o t ?_ ?_ ?_
  · intro s d _ h
    exact (compiled_act_now A fin hn s d).trans h
  · intro s o' hs _ h
    exact (compiled_recordOwn_now A fin hn s o' hs).trans h
  · exact compiled_process_now A fin hn nd.st o _

/-! ## The engine state across one event -/

variable [DecidableEq V]

private theorem stateBefore_succ_of_none {i : Nat} (he : rho.events[i]? = none) :
    rho.stateBefore (i + 1) = rho.stateBefore i := by
  simp [Model.Run.stateBefore, List.take_add_one, he]

private theorem stateBefore_succ_of_ne {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (shapeFamily A fin)) E).Object}
    (he : rho.events[i]? = some e) {v : V} (hne : e.node ≠ v) :
    rho.stateBefore (i + 1) v = rho.stateBefore i v := by
  rw [rho.stateBefore_succ he]
  cases e <;> simp only [Model.Event.node] at hne <;>
    simp only [Model.Run.step, Function.update_of_ne (Ne.symm hne)]

/-- Before the first event every node's clock is the initial `0`. -/
theorem engineState_zero_now (v : V) : (engineState A fin rho hn v 0).now = 0 :=
  compiled_init_now A fin hn (rho.ownKey v) _

/-- Past the last event the engine state is constant. -/
theorem engineState_succ_none (v : V) {i : Nat} (he : rho.events[i]? = none) :
    engineState A fin rho hn v (i + 1) = engineState A fin rho hn v i := by
  change (rho.stateBefore (i + 1) v).st.1 hn = (rho.stateBefore i v).st.1 hn
  rw [stateBefore_succ_of_none A fin rho he]

/-- An event of another node leaves the engine state, hence its clock, unchanged. -/
theorem engineState_succ_of_ne {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (shapeFamily A fin)) E).Object}
    (he : rho.events[i]? = some e) {v : V} (hne : e.node ≠ v) :
    engineState A fin rho hn v (i + 1) = engineState A fin rho hn v i := by
  change (rho.stateBefore (i + 1) v).st.1 hn = (rho.stateBefore i v).st.1 hn
  rw [stateBefore_succ_of_ne A fin rho he hne]

/-- After a tick of `v` at `t`, `v`'s clock is `t`. -/
theorem engineState_succ_tick_now {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) : (engineState A fin rho hn v (i + 1)).now = t := by
  change ((rho.stateBefore (i + 1) v).st.1 hn).now = t
  rw [rho.stateBefore_succ he]
  simp only [Model.Run.step, Function.update_self]
  exact run_tick_now A fin rho hn _ v t

/-- A delivery to `v` keeps `v`'s clock. -/
theorem engineState_succ_deliver_now {i : Nat} {v : V} {o} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    (engineState A fin rho hn v (i + 1)).now = (engineState A fin rho hn v i).now := by
  change ((rho.stateBefore (i + 1) v).st.1 hn).now = ((rho.stateBefore i v).st.1 hn).now
  rw [rho.stateBefore_succ he]
  simp only [Model.Run.step, Function.update_self]
  exact run_deliver_now A fin rho hn _ v o t

/-- After a restart of `v` at `t`, `v`'s clock is `t`. -/
theorem engineState_succ_restart_now {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    (engineState A fin rho hn v (i + 1)).now = t := by
  change ((rho.stateBefore (i + 1) v).st.1 hn).now = t
  rw [rho.stateBefore_succ he]
  simp only [Model.Run.step, Function.update_self]
  exact compiled_restore_now A fin hn _ _ _ t

/-! ## The last clock time -/

theorem lastClockNode_zero (v : V) : lastClockNode A fin rho v 0 = 0 := by rfl

theorem lastClockNode_succ_none (v : V) {i : Nat} (he : rho.events[i]? = none) :
    lastClockNode A fin rho v (i + 1) = lastClockNode A fin rho v i := by
  simp [lastClockNode, he]

theorem lastClockNode_succ_tick (v : V) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) : lastClockNode A fin rho v (i + 1) = t := by
  simp [lastClockNode, he]

theorem lastClockNode_succ_restart (v : V) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) : lastClockNode A fin rho v (i + 1) = t := by
  simp [lastClockNode, he]

theorem lastClockNode_succ_deliver (v : V) {i : Nat} {o} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    lastClockNode A fin rho v (i + 1) = lastClockNode A fin rho v i := by
  simp [lastClockNode, he]

theorem lastClockNode_succ_of_ne (v : V) {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (shapeFamily A fin)) E).Object}
    (he : rho.events[i]? = some e) (hne : e.node ≠ v) :
    lastClockNode A fin rho v (i + 1) = lastClockNode A fin rho v i := by
  cases e <;> simp only [Model.Event.node] at hne <;> simp [lastClockNode, he, hne]

/-! ## The stored clock -/

/-- **`SimulatesNodeAt.now`.** For every node, with no honesty premise, the stored clock before
event `i` is the time of the node's last tick or restart before `i`, and `0` if there is none. -/
theorem engineState_now (v : V) :
    ∀ i, (engineState A fin rho hn v i).now = lastClockNode A fin rho v i
  | 0 => (engineState_zero_now A fin rho hn v).trans (lastClockNode_zero A fin rho v).symm
  | i + 1 => by
    match he : rho.events[i]? with
    | none =>
      rw [engineState_succ_none A fin rho hn v he, lastClockNode_succ_none A fin rho v he]
      exact engineState_now v i
    | some e =>
      by_cases hv : e.node = v
      · cases e with
        | tick w t =>
          simp only [Model.Event.node] at hv
          subst hv
          rw [engineState_succ_tick_now A fin rho hn he, lastClockNode_succ_tick A fin rho _ he]
        | deliver w o t =>
          simp only [Model.Event.node] at hv
          subst hv
          rw [engineState_succ_deliver_now A fin rho hn he,
            lastClockNode_succ_deliver A fin rho _ he]
          exact engineState_now _ i
        | restart w t =>
          simp only [Model.Event.node] at hv
          subst hv
          rw [engineState_succ_restart_now A fin rho hn he,
            lastClockNode_succ_restart A fin rho _ he]
      · rw [engineState_succ_of_ne A fin rho hn he hv, lastClockNode_succ_of_ne A fin rho v he hv]
        exact engineState_now v i

end Consensus.Goldilocks.NodeEngine
