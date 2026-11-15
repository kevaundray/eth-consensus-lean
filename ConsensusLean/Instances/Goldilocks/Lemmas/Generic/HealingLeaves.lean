module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Obligations
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Deadline
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FrameWindowExists
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Healing
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLagCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Deadline
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.RecordsCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireClient
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.PreAdvanceFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.RiseWindow
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.StatementsBundle
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
import ConsensusLean.Lemmas.Tactic.Linarith

-- One module holds every generic healing leaf, so a single boundary exception
-- (scripts/boundaries.toml) and a single cut guard
-- (ConsensusLeanTest.Goldilocks.Generic.HealingLeavesCut) cover them all.
set_option linter.style.longFile 1800

public section

/-! # Generic healing leaves

The healing leaves proved once over any node AC: a node run under growing faults
(`Growing.LocalRun`) from any starts `ini`. The Goldilocks originals are instances.

Held attestations: an attestation on a block held at an observation honest at `t`, with a signer
honest at `t`, was signed before the cut (`held_att_signed_at_from`); two such attestations, with
a signer honest at a time after both observations, are not slashable (`held_atts_safe_at_from`).

Leaf 2, lower bound (`HZ_le_hmax_at_from`): after its relay obligation is paid, a receiver honest
at its cut has at least the snapshot height `HZ`. Relay and catch-up carry a held block of
height at least the receiver's `h_max` to the receiver (`held_of_relay_le_at_from`), and the
block's state is the same at both holders (`σ_eq_honest_at_from`).

Leaf 3 (`exists_frameWindow_seq_of_service_at_from`): per-cut height range and relay calls give
a frame window of the requested length, by the sequential pigeonhole over the cuts of nodes
honest at them with the merged-key lag between independently honest observations
(`frameKey'_lag_obs_from`).

Proposal membership and leaf 5, the round crossing (`proposal_mem_at_from`,
`round_cross_at_from`): an honest proposal is held by its proposer after its cut, and delivered
historical rows (`rows_delivered_service_at_from`, under the signed-row service clause) or higher
reports raise the proposal one height above the crossed block.

Leaf 2, upper bound (`hmax_le_of_noAdvance_at_from`): before any height advance by a signer
honest at it and at `c_z`, an honest observer's `h_max` is at most `HZ + 1`; an honest
attestation above it would have been signed before the observation.

Leaf 1 (`reset_of_height_advance_at_from`): a signing above `HZ` by a signer honest at it and at
`c_z` gives a reset no later; an honest attestation at `HZ + 1` below it was signed first, and the
earliest such signing is the reset.

Leaf 6c (`reset_of_high_source_at_from`): a high `fg_attest` source of a caller honest at it and
at `c_z` forces a reset no later; with no earlier high signing, the client's record has no lock or
sent content at that height, so the call signs and leaf 1 applies.

Leaf 6 (`reset_of_high_report_at_from`): a report of height at least `HZ + 1`, by a reporter
honest at it and at `c_z`, is followed in the same tick by its `fg_attest` call with the same
store, so leaf 6c gives a reset no later.

Leaf 7 (`sign_from_report_at_from`): an honest signing comes from the report of the `ac_to_fg`
cut just before it, at the same time and with the same store; under the requirements of the
node's AC start the report is held (`Healing.toFG_source_mem_from`), and its entry is the signed
target at the signed height.

Leaf 14 (`high_entry_eq_at_from`): two self-entries of equal height below two compatible honest
blocks are the same block. Both lie below the later block, which some node holds at an honest
observation, and along that store's ancestry the entry is constant at one height
(`Healing.Th_eq_of_anc`). The generic leaf compares its high origins by
`ACHealing.origins_comparable`.

Slot alignment (`exists_slot_align_of_grid`): on the four-delay grid, `s₀ = ⌈a_f / 4Δ⌉` has
`a_f ≤ t_{s₀}` and `4Δ·s₀ < a_f + 4Δ`.

Relay calls from wakefulness (`snapshotCall_of_awake_at_from`, `callLag_of_awake_at_from`): a
node awake on `[ḡ, b]` ticks at every public time there, and its restarts are at or before
`t_{slot(ḡ)+1} ≤ c_z`, so after `c_z` the call at a public time meets the relay deadline
(`Healing.callLag_of_awake`, `Healing.snapshotCall_of_awake` on the receiver's prefix, for any
node AC and any slot schedule).

Leaf 4 (`row_or_high_of_report_at_from`): a held report, before any height advance, either
supplies a row of a lower block of the same height signed while honest, or is strictly higher.
Its `fg_attest` call follows in the same tick with the same store; the lock at the height is
free (no advance) or names the entry (the client record's provenance, `Healing.record_facts`,
and its signed finality pairs, `Healing.signed_fin_justified`), so the client signs the row now or
signed it before (`Healing.client_progress_of_lock`).

Leaves 8 and 9 (`rounds_le_warm_proposal_at_of_healing`, `report_kind_of_warm_at_of_healing`)
are proved over any `ACHealing`: its `proposal_floor` puts a warm honest proposal at or above the
window floor. At a constant merged key `v ≥ 2HZ` the proposer's store has
`HZ + 1 ≤ floor + r(v)` (`Healing.le_floor_add_riseRounds`); a report at the proposal's height
above it is at or above the reader's floor, so above `h_j`, or at it with `J` below the report
(`ACHealing.report_in_frame`).

Leaf 10 (`reset_of_high_proposal_at_of_healing`), over any `ACHealing`: the leaf's premises are
`Premises`, so `ACHealing.report_follow` gives a node honest at the horizon a report above a warm
high proposal by the next slot's report deadline. The reader is honest at `c_z` and at the report,
the report is at least as high as the proposal in its store, and leaf 6 gives the reset.

Leaf 11 (`round_of_warm_at_of_healing`), over any `ACHealing`: an honest proposal comes from the
proposal call just before its block cut, and its parent is that call's duty head
(`proposalHead_of_proposesAt`). `ACHealing.report_follow` puts a report above the warm proposal
and below that head for every node honest at the later proposal; leaf 4, with leaf 9 for the
report kind, makes each report a row of the warm proposal or strictly higher, and leaf 5 crosses
one height. The report-delivery spacing `t_{s+1} + 2Δ + ΔF ≤ t_{s+δt}` gives the row deadline and
`δt ≥ 2`, so the later proposal is at or after `c_z`.

Leaf 12 (`high_row_source_at_of_healing`), over any `ACHealing`: a high signing by the horizon of
a premised reset comes from a report at the same time (leaf 7). `ACHealing.report_origin` gives
that report a high origin no later, and the signed entry, below the report, is below the origin in
the origin's store with the same replay state (`origin_below_report`).

Leaf 13 (`no_high_contest_at_of_healing`), over any `ACHealing`: in a contest at `h_max ≥ HZ + 2`,
`J` and the entry of the contested chain at `h_j` are two high self-entries, each left by a held
block. A held honest attestation on each (`Healing.honest_att_of_left`) was signed from a report
(leaf 7) whose origin holds the entry (`origin_below_report`); `ACHealing.origins_comparable`
makes the two origins compatible, and leaf 14 makes the entries equal, so `J` is below the chain.
-/

namespace Consensus.Goldilocks.Generic

/-- **Slot alignment** on the four-delay grid: `s₀ = ⌈a_f / 4Δ⌉` has `a_f ≤ t_{s₀}` and
`4Δ·s₀ < a_f + 4Δ`, for any schedule whose slot `s` starts at `s · 4Δ`. -/
theorem exists_slot_align_of_grid {P : Params} : exists_slot_align (P := P) := by
  intro hgrid af haf
  have h4D : 0 < 4 * P.Δ := by linarith only [P.hΔ]
  set s₀Z : ℤ := (af + 4 * P.Δ - 1) / (4 * P.Δ) with hs₀Z
  have hs₀lo := Int.ediv_mul_le (af + 4 * P.Δ - 1) h4D.ne'
  have hs₀hi := Int.lt_ediv_add_one_mul_self (af + 4 * P.Δ - 1) h4D
  rw [← hs₀Z] at hs₀lo hs₀hi
  have hs₀nn : 0 ≤ s₀Z := Int.ediv_nonneg (by linarith only [haf, h4D]) h4D.le
  have hs₀c : ((s₀Z.toNat : Nat) : ℤ) = s₀Z := Int.toNat_of_nonneg hs₀nn
  refine ⟨s₀Z.toNat, ?_, ?_⟩
  · rw [hgrid, hs₀c]
    linarith only [hs₀hi]
  · rw [hs₀c]
    linarith only [hs₀lo]

/-- An attestation on a block held at an observation honest at `t`, with a signer honest at `t`,
was signed before the cut, for any node run under growing faults from any starts `ini`. -/
theorem held_att_signed_at_from {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) {a : FG.Att P.n}
    (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload) (hav : a.val ∈ H t) :
    ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  have hXt : X ∈ ((tr.upTo t).state y i).fg.tree := by rw [Trace.upTo_state tr y hle]; exact hX
  rcases Healing.tree_accepted (h.upTo ht) hy hXt with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · have hacc' := ((Trace.upTo_callAt tr).mp hacc).2
    obtain ⟨k', hk', hs'⟩ := h.att_unforgeable y k a
      (h.antitone (hle k hk) hy) (Or.inr ⟨X, ⟨true, hacc'⟩, haX⟩)
      (h.antitone (hle k hk) hav)
    exact ⟨k', hk'.trans hk, hs'⟩

/-- **Held attestations at independently honest observations are not slashable**, for any node
run under growing faults from any starts `ini`. Attestations on blocks held by `y` (observed while
honest at `u`) and by `x` (observed while honest at `t`), with a signer honest at a time `d` after
both observations, were signed by that signer's client run on the prefix up to `d`, which client
safety (G0.5) keeps free of slashable pairs. -/
theorem held_atts_safe_at_from {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y x : Fin P.n} {m i : Nat} {u t d : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t) (hud : u ≤ d) (htd : t ≤ d)
    (a b : FG.Att P.n) (ha : ∃ Y ∈ (tr.state y m).fg.tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.state x i).fg.tree, b ∈ Y.fgPayload) (hav : a.val ∈ H d) :
    ¬ FG.slashable a b := fun hab => by
  obtain ⟨k, hk, hka⟩ := held_att_signed_at_from h hu hytime hy ha (h.antitone hud hav)
  obtain ⟨l, hl, hlb⟩ := held_att_signed_at_from h ht hxtime hx hb
    (hab.1 ▸ h.antitone htd hav)
  rw [← hab.1] at hlb
  have hka' : (tr.upTo d).SignAt a.val k a :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hytime k hk).trans hud, hka⟩
  have hlb' : (tr.upTo d).SignAt a.val l b :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hxtime l hl).trans htd, hlb⟩
  obtain ⟨inputs, hin, hs⟩ :=
    Store.signed_run_of_exec (Compose.fg_exec (h.upTo (hu.trans hud))) hav (max k l + 1)
  exact FG.client_safety P.fg a.val inputs hin
    a (hs k (by omega) a ⟨_, Compose.projFG_callAt.mpr hka'.choose_spec⟩)
    b (hs l (by omega) b ⟨_, Compose.projFG_callAt.mpr hlb'.choose_spec⟩) hab

/-! ## Leaf 2, upper bound -/

/-- Before any height advance, an honest observer's cached height is at most the snapshot
height plus one, with the quorum budget charged at the later of the snapshot and observation. -/
theorem hmax_le_of_noAdvance_at_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} {g T : Time} {y : Fin P.n} {i : Nat}
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hna : NoAdvance tr H g T) (hy : y ∈ H (tr.time i))
    (hq : (H (max (Healing.cutZ P g) (tr.time i)))ᶜ.ncard < P.fg.q)
    (hiT : tr.time i < T) :
    (tr.state y i).fg.hmax ≤ Healing.Growing.HZ tr H g + 1 := by
  have hr := hrun.upTo (hrun.time_nonneg i)
  have hs : (tr.upTo (tr.time i)).state y i = tr.state y i :=
    Trace.upTo_state tr y (fun _ hk => hrun.time_mono hk.le)
  have hR := Compose.fg_reachable hr hy i
  obtain ⟨_, _, _, _, _, ⟨X, hX, hXh⟩, _⟩ := Store.cache_invariants _ _ _ _ hR
  by_contra hlt
  rw [← hs] at hlt
  obtain ⟨Y, hYX, a, ha, haH, hah⟩ := Healing.Store.exists_honest_att_of_lt hR hq hX
    (Healing.Growing.HZ tr H g + 1) (by omega) (by omega)
  have hY : Y ∈ ((tr.upTo (tr.time i)).state y i).fg.tree := by
    by_cases he : Y = X
    · exact he ▸ hX
    · exact (Anc.mem hYX he).1
  rcases Healing.tree_accepted hr hy hY with rfl | ⟨k, hki, hA⟩
  · cases ha
  obtain ⟨j, hjk, hj⟩ := hr.att_unforgeable y hy k a
    (Or.inr ⟨Y, ⟨true, hA⟩, ha⟩) (hrun.antitone (le_max_right _ _) haH)
  have hjT : tr.time j < T := (hrun.time_mono (by omega)).trans_lt hiT
  obtain ⟨hjt, hj⟩ := (RunTrace.upTo_signAt tr).mp hj
  have := hna a.val j a (hrun.antitone (max_le_max le_rfl hjt) haH) hj hjT
  omega

/-! ## Leaf 1 -/

/-- A high signing honest at its cut and at the snapshot gives a reset no later. -/
theorem reset_of_height_advance_at_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} {g : Time} {y : Fin P.n} {k : Nat} {att : FG.Att P.n}
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hq : (H (max (Healing.cutZ P g) (tr.time k)))ᶜ.ncard < P.fg.q)
    (hyz : y ∈ H (max (Healing.cutZ P g) (tr.time k)))
    (hs : tr.SignAt y k att) (hh : Healing.Growing.HZ tr H g + 1 ≤ att.h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time k := by
  classical
  have hr := hrun.upTo (hrun.time_nonneg k)
  have hy := hrun.antitone (le_max_right _ _) hyz
  have hex₀ : ∃ j z a, z ∈ H (max (Healing.cutZ P g) (tr.time j)) ∧ tr.SignAt z j a ∧
      a.h = Healing.Growing.HZ tr H g + 1 ∧ tr.time j ≤ tr.time k := by
    rcases hh.lt_or_eq with hlt | heq
    · have hs' := (RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩
      obtain ⟨E, hE, _, hEh⟩ := Healing.signAt_entry_from hr hy hs'
      obtain ⟨Y, hYE, a, ha, haH, hah⟩ := Healing.Store.exists_honest_att_of_lt
        (Compose.fg_reachable hr hy k) hq hE (Healing.Growing.HZ tr H g + 1)
        (by omega) (by omega)
      have hY : Y ∈ ((tr.upTo (tr.time k)).state y k).fg.tree := by
        by_cases he : Y = E
        · exact he ▸ hE
        · exact (Anc.mem hYE he).1
      obtain ⟨src, hc⟩ := hs'
      obtain ⟨j, hj, hjk⟩ := Healing.signed_before_attest hr hy hc hY ha
        (hrun.antitone (le_max_right _ _) haH)
      obtain ⟨hjt, hsign⟩ := (RunTrace.upTo_signAt tr).mp hj
      exact ⟨j, a.val, a, hrun.antitone (max_le_max le_rfl hjt) haH, hsign, hah, hjt⟩
    · exact ⟨k, y, att, hyz, hs, heq.symm, le_rfl⟩
  obtain ⟨j, z, att, hz, hs, hh, hjk⟩ := hex₀
  have hex : ∃ j z att, z ∈ H (max (Healing.cutZ P g) (tr.time j)) ∧ tr.SignAt z j att ∧
      att.h = Healing.Growing.HZ tr H g + 1 := ⟨j, z, att, hz, hs, hh⟩
  obtain ⟨v, c, hv, hc, hch⟩ := Nat.find_spec hex
  have hR : Healing.Growing.IsReset tr H g (tr.time (Nat.find hex)) :=
    ⟨⟨v, Nat.find hex, c, hv, hc, hch, rfl⟩, by
      intro v i c hv hc hch
      exact hrun.time_mono (Nat.find_min' hex ⟨v, c, hv, hc, hch⟩)⟩
  exact ⟨_, hR, (hR.2 z j att hz hs hh).trans hjk⟩

/-! ## Leaf 6c -/

/-- A high FG source forces a reset, including when its client suppresses signing. -/
theorem reset_of_high_source_at_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} {g : Time} {y : Fin P.n} {k : Nat} {C : A.Blk}
    {s : Option (FG.Att P.n)}
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hyz : y ∈ H (max (Healing.cutZ P g) (tr.time k)))
    (hq : (H (max (Healing.cutZ P g) (tr.time k)))ᶜ.ncard < P.fg.q)
    (hc : tr.CallAt y k (.fg (.attest C s)))
    (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time k := by
  classical
  have hy := hrun.antitone (le_max_right _ _) hyz
  have hl := hrun.upTo (hrun.time_nonneg k)
  have hst := Trace.upTo_state tr y (i := k) (fun q hq => hrun.time_mono hq.le)
  have hr := Compose.fg_reachable hl hy k
  rw [hst] at hr
  have he : ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h =
      ((tr.state y k).fg.σ C.root).h := by
    rcases hC : (tr.state y k).fg.blocks C.root with _ | X
    · rw [Healing.Store.σ_of_blocks_none hr hC]
      exact congrArg FG.ChainState.h (Healing.Store.σ_genesis hr)
    · have hXr := Store.Reachable.blocks_root hr hC
      have hX : X ∈ (tr.state y k).fg.tree := by
        change (tr.state y k).fg.blocks X.root = some X
        rw [hXr]; exact hC
      obtain ⟨⟨E, _, hEr, _, hEh, _⟩, _⟩ := Store.entry_state_of_source _ _ _ _ hr X hX
      rw [← hXr, ← hEr]
      exact hEh
  by_cases hprev : ∃ j < k, ∃ att, tr.SignAt y j att ∧
      Healing.Growing.HZ tr H g + 1 ≤ att.h
  · obtain ⟨j, hj, att, hs, hh⟩ := hprev
    have hjt := hrun.time_mono hj.le
    have hjz := max_le_max (le_refl (Healing.cutZ P g)) hjt
    have hqj : (H (max (Healing.cutZ P g) (tr.time j)))ᶜ.ncard < P.fg.q := by
      exact lt_of_le_of_lt (Set.ncard_le_ncard (Set.compl_subset_compl.mpr
        (hrun.antitone hjz)) (Set.toFinite _)) hq
    obtain ⟨a, ha, haj⟩ := reset_of_height_advance_at_from hrun hqj
      (hrun.antitone hjz hyz) hs hh
    exact ⟨a, ha, haj.trans hjt⟩
  have hlock : (tr.state y k).record.lock ((tr.state y k).fg.σ C.root).h = none := by
    by_contra hn
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hn
    obtain ⟨j, hj, att, hs, hfin⟩ :=
      (Healing.client_record_origin_from hl hy _ r k).2 (by rwa [hst])
    have hw := (Healing.signAt_wellFormed_from hl hy hs).2
      (((tr.state y k).fg.σ C.root).h, r) (by simp [hfin])
    exact hprev ⟨j, hj, att, ((RunTrace.upTo_signAt tr).mp hs).2, by omega⟩
  have hsent : ∀ b ∈ (tr.state y k).record.sent,
      b.1 ≠ ((tr.state y k).fg.σ C.root).h := by
    intro b hb hbh
    obtain ⟨j, hj, att, hs, heq⟩ := Healing.sent_origin_from hl hy k (by rwa [hst])
    have hah : att.h = b.1 := congrArg Prod.fst heq
    exact hprev ⟨j, hj, att, ((RunTrace.upTo_signAt tr).mp hs).2, by omega⟩
  have hany (τ : Bool) : (tr.state y k).record.sent.any (fun b =>
      b.1 = ((tr.state y k).fg.σ C.root).h ∧ (!τ ∨ b.2.1 =
        ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th)) = false := by
    apply List.any_eq_false.2
    intro b hb
    simp [hsent b hb]
  cases s with
  | some att =>
    have hcl := (hrun.cutLaw y k _ hc hy).1
    apply reset_of_height_advance_at_from hrun hq hyz ⟨C, hc⟩
    rw [(Healing.Store.createAtt_eq hcl).1, he]
    exact hh
  | none =>
    have hcl := (hrun.cutLaw y k _ hc hy).1
    exfalso
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = none at hcl
    have hτ : ∃ τ, (tr.state y k).record.heightPair ((tr.state y k).fg.σ C.root).h
        ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th =
        some (((tr.state y k).fg.σ C.root).h,
          ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th, τ) := by
      unfold FG.Record.heightPair
      simp only [hlock, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      split_ifs <;> exact ⟨_, rfl⟩
    obtain ⟨τ, hτ⟩ := hτ
    unfold FG.Record.createAtt at hcl
    rw [he, hτ] at hcl
    dsimp only at hcl
    rw [hany τ] at hcl
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hcl

/-! ## Leaf 6 -/

/-- A high report gives a high FG source in the same tick, hence a reset no later. -/
theorem reset_of_high_report_at_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} {g : Time} {y : Fin P.n} {i : Nat} {R : A.Blk}
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hyz : y ∈ H (max (Healing.cutZ P g) (tr.time i)))
    (hq : (H (max (Healing.cutZ P g) (tr.time i)))ᶜ.ncard < P.fg.q)
    (hR : ReportAt tr y i R)
    (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time i := by
  have hy := hrun.antitone (le_max_right _ _) hyz
  have hr := hrun.upTo (hrun.time_nonneg i)
  have hst := Trace.upTo_state tr y (i := i) (fun q hq => hrun.time_mono hq.le)
  obtain ⟨ell, hc, hto, hres⟩ := hR
  have hc' : (tr.upTo (tr.time i)).CallAt y i (.ac ell) :=
    (Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩
  have hres' : (A.toFG ((tr.upTo (tr.time i)).state y i).ac
      ell.frame (tr.time i)).2 = some R := by rwa [hst]
  obtain ⟨s, hatt, ht, hfg⟩ := Healing.toFG_attest hr hy hc' hto hres'
  have ht' : tr.time (i + 1) = tr.time i := ht
  have hs1 := Trace.upTo_state tr (d := tr.time i) y (i := i + 1)
    (fun q hq => hrun.time_mono (by omega))
  have hatt' := ((Trace.upTo_callAt tr).mp hatt).2
  rw [hs1, hst] at hfg
  have hh' : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y (i + 1)).fg.σ R.root).h := by
    rwa [hfg]
  obtain ⟨a, ha, hat⟩ := reset_of_high_source_at_from hrun
    (ht' ▸ hyz) (ht' ▸ hq) hatt' hh'
  exact ⟨a, ha, by rwa [ht'] at hat⟩

/-! ## Leaf 7 -/

/-- An honest signing comes from the report of the `ac_to_fg` cut just before it, at the same
time: the report is held, its entry is the signed target, and the signed height is its height. -/
theorem sign_from_report_at_from {P : Params} {A : NodeAC P}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
    {ini : Fin P.n → A.State} {y : Fin P.n} {k : Nat} {att : FG.Att P.n}
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hq : ∀ y, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hy : y ∈ H (tr.time k)) (hs : tr.SignAt y k att) :
    ∃ i < k, ∃ R, ReportAt tr y i R ∧ tr.time i = tr.time k ∧
      att.h ≤ ((tr.state y i).fg.σ R.root).h ∧
      ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E R ∧ E.root = att.T ∧
        ((tr.state y i).fg.σ E.root).h = att.h ∧ ((tr.state y i).fg.σ E.root).Th = E.root := by
  have hr := hrun.upTo (hrun.time_nonneg k)
  obtain ⟨C, hc⟩ := hs
  obtain ⟨i, rfl, ℓ, hci, hto, ht, hC, hfg⟩ :=
    Compose.attest_source hr hy ((Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩)
  have hCt := Healing.toFG_source_mem_from hr hy (hq y) hci hto hC
  have hreach := Compose.fg_reachable hr hy i
  have ht' : tr.time i = tr.time (i + 1) := ht
  have hsi := Trace.upTo_state tr (d := tr.time (i + 1)) y (i := i)
    (fun q hq => hrun.time_mono (by omega))
  have hsk := Trace.upTo_state tr (d := tr.time (i + 1)) y (i := i + 1)
    (fun q hq => hrun.time_mono (by omega))
  rw [hsi] at hC hCt hreach
  rw [hsk, hsi] at hfg
  obtain ⟨⟨E, hE, hEr, hEC, hEh, hETh⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hreach C hCt
  obtain ⟨hah, haT⟩ := Healing.Store.createAtt_eq (hrun.cutLaw y (i + 1) _ hc hy).1
  rw [hfg, ← hEr] at hah haT
  have hETh' : ((tr.state y i).fg.σ E.root).Th = E.root := by rw [hETh, hEr]
  refine ⟨i, by omega, C, ⟨ℓ, ((Trace.upTo_callAt tr).mp hci).2, hto, hC⟩, ht',
    by rw [hah, hEh], E, hE, hEC, by rw [haT, hETh'], hah.symm, hETh'⟩

/-! ## Relay calls from wakefulness -/

section CallLag

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

open SA (gbar)
open Healing (FirstCutAfter cutZ)

/-- Public ticks supply the snapshot and the snapshot relay call before an honest receiver's
cut at or after `c_z + Δ + 1`: the static `Healing.snapshot_of_awake` and
`Healing.snapshotCall_of_awake` on the receiver's prefix. -/
theorem snapshotCall_of_awake_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini) {g b : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    {z : Fin P.n} {m : Nat} (hz : z ∈ H (tr.time m))
    (hfit : cutZ P g + P.Δ + 1 ≤ tr.time m) (hmb : tr.time m ≤ b) :
    (∃ j, FirstCutAfter tr j (cutZ P g)) ∧
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (cutZ P g) g) P.Δ ≤ tr.time j := by
  have hr := hrun.upTo (hrun.time_nonneg m)
  have ha : ∀ y ∈ H (tr.time m), ∀ t, gbar g ≤ t → t ≤ tr.time m →
      (tr.upTo (tr.time m)).awake y t := fun y hy t ht htm =>
    ⟨hawake y t (hrun.antitone htm hy) ht (htm.trans hmb), htm⟩
  obtain ⟨j, hj, -⟩ := Healing.snapshot_of_awake hr ha ⟨z, hz⟩
    (show cutZ P g + P.Δ ≤ tr.time m by linarith)
  refine ⟨⟨j, hj⟩, ?_⟩
  obtain ⟨j, hjm, hc, hd⟩ := Healing.snapshotCall_of_awake hr ha hfit
    (T := tr.time m + 1) le_rfl z hz m le_rfl
    (show tr.time m < tr.time m + 1 by linarith)
  have hjt := ((RunTrace.upTo_isCall tr).mp hc).1
  refine ⟨j, hjm, ((RunTrace.upTo_isCall tr).mp hc).2, ?_⟩
  rwa [RunTrace.upTo_deadline hrun.time_mono hjt] at hd

/-- Wakefulness supplies a relay call before an independently honest receiver cut, at the
two-delay lag: the static `Healing.callLag_of_awake` on the receiver's prefix. -/
theorem callLag_of_awake_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini) {g b lo : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hlo : cutZ P g ≤ lo) {z : Fin P.n} {i m : Nat}
    (hz : z ∈ H (tr.time m)) (hi : lo ≤ tr.time i)
    (him : tr.time i + 2 * P.Δ ≤ tr.time m) (hmb : tr.time m ≤ b) :
    ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) P.Δ ≤ tr.time j := by
  have hr := hrun.upTo (hrun.time_nonneg m)
  have ha : ∀ y ∈ H (tr.time m), ∀ t, gbar g ≤ t → t ≤ tr.time m →
      (tr.upTo (tr.time m)).awake y t := fun y hy t ht htm =>
    ⟨hawake y t (hrun.antitone htm hy) ht (htm.trans hmb), htm⟩
  obtain ⟨j, hjm, hc, hd⟩ := Healing.callLag_of_awake hr ha hlo
    (T := tr.time m + 1) le_rfl z hz i m hi him
      (show tr.time m < tr.time m + 1 by linarith)
  have hjt := ((RunTrace.upTo_isCall tr).mp hc).1
  refine ⟨j, hjm, ((RunTrace.upTo_isCall tr).mp hc).2, ?_⟩
  rwa [RunTrace.upTo_deadline hrun.time_mono hjt] at hd

end CallLag

/-! ## Leaf 2, lower bound -/

section HZLowerBound

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

open SA (gbar)
open Healing (FirstCutAfter cutZ)
open Healing.Growing (HZ CatchRun)

/-- Reachability at a held-state observation, not necessarily the time of cut `i`. -/
theorem fg_reachable_at_from (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) :
    (tr.state y i).fg.Reachable A.genesisPayload := by
  simpa only [Trace.upTo_state tr y hle] using Compose.fg_reachable (h.upTo ht) hy i

/-- Ancestry in a tree observed while honest lies in the historical honest universe. -/
theorem honest_anc_of_store_anc_at_from {y : Fin P.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {B C : A.Blk} (h : (tr.state y k).fg.Anc B C) :
    Anc (tr.HonestBlocksAt H) B C :=
  h.mono fun _ hB => ⟨y, k, t, ht, hle, hy, hB⟩

/-- A held block's replay state is identical at two independently honest observations. -/
theorem σ_eq_honest_at_from (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin P.n} {i j : Nat} {t u : Time}
    (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t)
    (hu : 0 ≤ u) (hle' : ∀ q < j, tr.time q ≤ u) (hz : z ∈ H u)
    {B : A.Blk} (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root :=
  Healing.Store.σ_eq_of_mem (fg_reachable_at_from h ht hle hy) (fg_reachable_at_from h hu hle' hz)
    (Compose.Growing.honest_blocks_coherent_local h hnc).1
    (fun _ hX => ⟨y, i, t, ht, hle, hy, hX⟩)
    (fun _ hX => ⟨z, j, u, hu, hle', hz, hX⟩) hBy hBz

/-- Strict-height finalized ancestry for two independently honest held-state observations. -/
theorem F_anc_of_hmax_le_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin P.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * P.fg.q - P.n)
    {B : A.Blk} (hB : B ∈ (tr.state x i).fg.tree)
    (hle : (tr.state y m).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h) :
    Anc (tr.HonestBlocksAt H) (tr.state y m).fg.F B :=
  honest_anc_of_store_anc_at_from ht hxtime hx <| Store.F_anc_of_hmax_le_of_safe
    (fg_reachable_at_from h hu hytime hy) (fg_reachable_at_from h ht hxtime hx)
    (Compose.Growing.honest_blocks_coherent_local h hnc)
    (fun _ hX => ⟨y, m, u, hu, hytime, hy, hX⟩)
    (fun _ hX => ⟨x, i, t, ht, hxtime, hx, hX⟩) hf
    (held_atts_safe_at_from h hu hytime hy ht hxtime hx (le_max_left _ _) (le_max_right _ _))
    hB hle

/-- Relay and catch-up carry a held block to a receiver whose height has not passed it. -/
theorem held_of_relay_le_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ τ : Time}
    (hsvc : Service tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin P.n} {i m : Nat} (hτ0 : 0 ≤ τ) (hx : x ∈ H τ)
    (hz : z ∈ H (tr.time m))
    (hf : (H (max τ (tr.time m)))ᶜ.ncard < 2 * P.fg.q - P.n)
    {B : A.Blk} (hB : B ∈ (tr.state x i).fg.tree)
    (hh : (tr.state z m).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h)
    (hτ : ∀ k < i, tr.time k ≤ τ)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max τ g) P.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) : B ∈ (tr.state z m).fg.tree := by
  have hm0 := h.time_nonneg m
  have hm : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => h.time_mono hk.le
  have hs : ∀ j ≤ m, (tr.upTo (tr.time m)).state z j = tr.state z j :=
    fun j hj => Trace.upTo_state tr z (fun k hk => h.time_mono (by omega))
  have hr := h.upTo hm0
  have hF : ∀ j ≤ m, Anc (tr.HonestBlocksAt H) (tr.state z j).fg.F B := by
    intro j hj
    have hheight := Healing.hmax_mono hr hz hj
    dsimp only at hheight
    rw [hs j hj, hs m le_rfl] at hheight
    apply F_anc_of_hmax_le_at_from h hnc hm0
      (fun k hk => h.time_mono (by omega)) hz hτ0 hτ hx
      (by rwa [max_comm]) hB (hheight.trans hh)
  have hlift : ∀ k, k + 1 ≤ m → tr.AcceptAt z k B → B ∈ (tr.state z m).fg.tree := by
    intro k hkm ha
    have ha' : (tr.upTo (tr.time m)).AcceptAt z k B :=
      (RunTrace.upTo_acceptAt tr).mpr ⟨h.time_mono (by omega), ha⟩
    have hmem := Healing.accept_mem_from hr hz ha'
    have := Compose.tree_mono hr hz hkm hmem
    rwa [hs m le_rfl] at this
  have hB' : B ∈ ((tr.upTo τ).state x i).fg.tree := by
    rwa [Trace.upTo_state tr x hτ]
  rcases Healing.tree_accepted (h.upTo hτ0) hx hB' with he | ⟨k, hk, ha⟩
  · rw [he]
    exact Healing.Store.genesis_mem (fg_reachable_at_from h hm0 hm hz)
  have ha := ((RunTrace.upTo_acceptAt tr).mp ha).2
  have hxk := h.antitone (hτ k hk) hx
  by_cases hg : g ≤ tr.time k
  · obtain ⟨j, hjm, hcj, hdl⟩ := hcall
    have hdl' := (tr.deadline_mono z j (max_le_max (hτ k hk) le_rfl) P.Δ).trans hdl
    obtain ⟨k', hk'j, ha', -⟩ := hsvc.relay x k B hxk ha hg z j
      (h.antitone (h.time_mono hjm.le) hz) hcj hdl' (hF j hjm.le)
    exact hlift k' (by omega) ha'
  · obtain ⟨j₀, hfirst, hj₀⟩ := Healing.exists_firstCutFrom_le hcm
    obtain ⟨k', hk', ha'⟩ := hcatch x k B hxk ha
      (lt_of_lt_of_le (not_le.mp hg) (le_max_left _ _)) z j₀
      (h.antitone hcm hz) hfirst (hF j₀ hj₀)
    exact hlift k' (by omega) ha'

/-- The snapshot height is attained by a member of its own honest cohort. -/
theorem exists_HZ_holder_at_from {g : Time} (hH : (H (cutZ P g)).Nonempty) {j : Nat}
    (hj : FirstCutAfter tr j (cutZ P g)) :
    ∃ x ∈ H (cutZ P g), (tr.state x j).fg.hmax = HZ tr H g := by
  obtain ⟨y, hy⟩ := hH
  have hne : {h | ∃ y ∈ H (cutZ P g), ∃ j,
      FirstCutAfter tr j (cutZ P g) ∧ (tr.state y j).fg.hmax = h}.Nonempty :=
    ⟨_, y, hy, j, hj, rfl⟩
  obtain ⟨x, hx, j', hj', he⟩ := Nat.sSup_mem hne
    (((Set.finite_range fun z => (tr.state z j).fg.hmax).subset (by
      rintro _ ⟨z, -, j', hj', rfl⟩
      obtain rfl := hj'.unique hj
      exact ⟨z, rfl⟩)).bddAbove)
  obtain rfl := hj'.unique hj
  exact ⟨x, hx, he⟩

/-- **Leaf 2, lower bound.** After its relay obligation is paid, a receiver honest at its cut
has at least the snapshot height, for any node run under growing faults from any starts `ini`. -/
theorem HZ_le_hmax_at_from (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hsvc : Service tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    (hH : (H (cutZ P g)).Nonempty) (hsnap : ∃ j, FirstCutAfter tr j (cutZ P g))
    {z : Fin P.n} {m : Nat} (hz : z ∈ H (tr.time m))
    (hf : (H (max (cutZ P g) (tr.time m)))ᶜ.ncard < 2 * P.fg.q - P.n)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (cutZ P g) g) P.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) : HZ tr H g ≤ (tr.state z m).fg.hmax := by
  obtain ⟨j, hj⟩ := hsnap
  obtain ⟨x, hx, hxe⟩ := exists_HZ_holder_at_from hH hj
  have hc0 : 0 ≤ cutZ P g := by
    have := P.slotTime_strictMono.monotone (Nat.zero_le (P.slotOf (gbar g) + 3))
    rwa [P.slotTime_zero] at this
  have hRx := fg_reachable_at_from h hc0 hj.1 hx
  have hm : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => h.time_mono hk.le
  have hRz := fg_reachable_at_from h (h.time_nonneg m) hm hz
  obtain ⟨-, -, -, -, -, ⟨B, hB, hBh⟩, -⟩ := Store.cache_invariants _ _ _ _ hRx
  by_cases hle : HZ tr H g ≤ (tr.state z m).fg.hmax
  · exact hle
  have hBz := held_of_relay_le_at_from h hnc hsvc hcatch hc0 hx hz hf hB
    (by omega) hj.1 hcall hcm
  have he := σ_eq_honest_at_from h hnc hc0 hj.1 hx (h.time_nonneg m) hm hz hB hBz
  have hh := (Store.cache_invariants _ _ _ _ hRz).2.2.2.2.1 B hBz
  rw [← he] at hh
  omega

end HZLowerBound

/-! ## Store ancestry below honest blocks -/

section StoreAnc

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- Historical ancestry descends into the reader's actual held tree, for any node run under
growing faults from any starts `ini`. -/
theorem store_anc_of_honest_anc_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin P.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {B C : A.Blk} (hBC : Anc (tr.HonestBlocksAt H) B C) (hC : C ∈ (tr.state y k).fg.tree) :
    (tr.state y k).fg.Anc B C := by
  have hs := Trace.upTo_state tr y hle
  have hc : C ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, k, by rwa [hs]⟩
  have hanc := RunTrace.anc_upTo_of_right h hnc ht hc hBC
  rw [← hs]
  exact Healing.store_anc_of_honest_anc_from (h.upTo ht)
    (Compose.NoCollRun.upTo hnc t) hy hanc (by rwa [hs])

end StoreAnc

/-! ## Leaf 3, the frame window -/

section FrameWindowLeaf

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

open SA (gbar)
open Healing.Growing (CatchRun)

/-- The merged frame key of the generic statements is the merged frame key of the stores. -/
theorem frameKey'_eq (st : Store P A.Payload) : frameKey' A st = Healing.frameKey' st := by
  rw [Healing.frameKey'_def, Healing.keyMerge_eq, Healing.frameKey_def]
  rfl

/-- `Σ.J` of two stores observed while honest with equal `h_j` agree. -/
private theorem J_eq_of_hj_eq_obs_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin P.n} {m i : Nat} {u t : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hf : (H (max u t))ᶜ.ncard < 2 * P.fg.q - P.n)
    (he : (tr.state y m).fg.hj = (tr.state x i).fg.hj) :
    (tr.state y m).fg.J = (tr.state x i).fg.J :=
  Healing.Store.J_eq_of_cache_hj_eq_of_safe (fg_reachable_at_from h hu hytime hy)
    (fg_reachable_at_from h ht hxtime hx) (Compose.Growing.honest_blocks_coherent_local h hnc)
    (fun _ hX => ⟨y, m, u, hu, hytime, hy, hX⟩) (fun _ hX => ⟨x, i, t, ht, hxtime, hx, hX⟩) hf
    (held_atts_safe_at_from h hu hytime hy ht hxtime hx (le_max_left _ _) (le_max_right _ _))
    he

/-- `h_j < h_max` at a store observed while honest. -/
private theorem hj_lt_hmax_obs_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t)
    (hy : y ∈ H t) : (tr.state y i).fg.hj < (tr.state y i).fg.hmax :=
  Healing.Store.hj_lt_hmax_of_reachable (fg_reachable_at_from h ht hle hy)

/-- **The frame-key lag** with the source `x` honest at its cut `i` and the receiver `z` honest at
its cut `m`, after a call of `z` at or after the relay deadline of `i`. -/
theorem frameKey_lag_obs_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    (hsvc : Service tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin P.n} {i m : Nat} (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (him : tr.time i ≤ tr.time m) (hmb : tr.time m ≤ b)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) P.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    Healing.frameKey (tr.state x i).fg ≤ Healing.frameKey (tr.state z m).fg := by
  have hi0 := h.time_nonneg i
  have hm0 := h.time_nonneg m
  have hxle : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => h.time_mono hk.le
  have hzle : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => h.time_mono hk.le
  have hfmi : (H (max (tr.time i) (tr.time m)))ᶜ.ncard < 2 * P.fg.q - P.n := by
    rw [max_eq_right him]; exact hf _ hm0 hmb
  exact Healing.frameKey_le_of_relay (fg_reachable_at_from h hi0 hxle hx)
    (fg_reachable_at_from h hm0 hzle hz)
    (Compose.Growing.honest_blocks_coherent_local h hnc)
    (fun _ hX => ⟨x, i, tr.time i, hi0, hxle, hx, hX⟩)
    (fun _ hX => ⟨z, m, tr.time m, hm0, hzle, hz, hX⟩) (hf _ hm0 hmb)
    (held_atts_safe_at_from h hm0 hzle hz hi0 hxle hx le_rfl him)
    (held_atts_safe_at_from h hm0 hzle hz hm0 hzle hz le_rfl le_rfl)
    (fun _ _ hBC hC => store_anc_of_honest_anc_at_from h hnc hi0 hxle hx hBC hC)
    (fun _ _ hBC hC => store_anc_of_honest_anc_at_from h hnc hm0 hzle hz hBC hC)
    (fun _ hB hh => held_of_relay_le_at_from h hnc hsvc hcatch hi0 hx hz hfmi hB hh hxle hcall
      hcm)

/-- **The merged-key lag** between independently honest observations. -/
theorem frameKey'_lag_obs_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    (hsvc : Service tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin P.n} {i m : Nat} (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (him : tr.time i ≤ tr.time m) (hmb : tr.time m ≤ b)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) P.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    Healing.frameKey' (tr.state x i).fg ≤ Healing.frameKey' (tr.state z m).fg :=
  (Healing.frameKey'_def _).symm ▸ (Healing.frameKey'_def _).symm ▸ Healing.keyMerge_mono
    (frameKey_lag_obs_from h hnc hf hsvc hcatch hx hz him hmb hcall hcm)

/-- A merged key that is constant over the cuts of `[lo, hi]` of nodes honest at them gives a
`FrameWindow`, when `hi ≤ b`. -/
theorem frameWindow_of_frameKey'_eq_obs_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    {lo hi : Time} (hhi : hi ≤ b)
    (hK : ∀ y z i m, y ∈ H (tr.time i) → z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i ≤ hi → lo ≤ tr.time m → tr.time m ≤ hi →
      Healing.frameKey' (tr.state y i).fg = Healing.frameKey' (tr.state z m).fg) :
    ∃ floor kindJ J, FrameWindow tr H lo hi floor kindJ J := by
  have hle : ∀ i k, k < i → tr.time k ≤ tr.time i := fun _ _ hk => h.time_mono hk.le
  obtain ⟨floor, kindJ, J, h1, h2, h3⟩ := Healing.frameData_of_frameKey'_eq
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => (tr.state y i).fg)
    (P.genesisBlock A.genesisPayload)
    (fun y i hy => hj_lt_hmax_obs_from h (h.time_nonneg i) (hle i) hy) hK
    (fun y z i m hy hz _ hi _ hm he => J_eq_of_hj_eq_obs_from h hnc (h.time_nonneg i) (hle i) hy
      (h.time_nonneg m) (hle m) hz
      (hf _ ((h.time_nonneg i).trans (le_max_left _ _)) (max_le (hi.trans hhi) (hm.trans hhi)))
      he)
  exact ⟨floor, kindJ, J, ⟨h1, h2, h3⟩⟩

/-- **Leaf 3.** Per-cut height range and relay calls produce a frame window, by the sequential
pigeonhole over the cuts of nodes honest at them with the merged-key lag between independently
honest observations, for any node run under growing faults from any starts `ini`. -/
theorem exists_frameWindow_seq_of_service_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    (hsvc : Service tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {lo lam T : Time} {hz : Nat} (len : Nat → Time)
    (hlen : ∀ v, 0 ≤ len v) (hlam : 0 ≤ lam) (hlo : gbar g + κ ≤ lo) (hTb : T ≤ b)
    (hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < T →
      hz ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ hz + 1)
    (hcall : ∀ z i m, z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) P.Δ ≤ tr.time j)
    (hT : lo + ∑ j ∈ Finset.range 5, (len (2 * hz + j) + lam) < T) :
    ∃ v, 2 * hz ≤ v ∧ v ≤ 2 * hz + 4 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam) ∧
      (∀ y i, y ∈ H (tr.time i) → a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey' A (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, FrameWindow tr H a (a + len v) floor kindJ J := by
  obtain ⟨v, hv1, hv2, a, h1, h2, hK⟩ := Healing.Growing.exists_const_window_seq
    (fun y i => y ∈ H (tr.time i)) tr.time (fun y i => Healing.frameKey' (tr.state y i).fg)
    (2 * hz) 4 len hlen hlam
    (fun y i hy h1 h2 => by
      have := hrange y i hy h1 h2
      exact Healing.frameKey'_bounds this.1 this.2)
    (fun x z i m hx hz' hi _ him hmT => frameKey'_lag_obs_from h hnc hf hsvc hcatch hx hz'
      ((le_add_of_nonneg_right hlam).trans him) (hmT.le.trans hTb)
      (hcall z i m hz' hi him hmT) (hlo.trans (hi.trans ((le_add_of_nonneg_right hlam).trans him))))
    hT
  -- the window ends before `T`
  have hS : ∀ j, j ≤ 4 → ∑ i ∈ Finset.range (j + 1), (len (2 * hz + i) + lam) ≤
      ∑ i ∈ Finset.range 5, (len (2 * hz + i) + lam) := fun j hj =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      fun i _ _ => add_nonneg (hlen _) hlam
  have hend : a + len v < T := by
    have := hS (v - 2 * hz) (by omega)
    linarith
  refine ⟨v, hv1, hv2, a, h1, h2,
    fun y i hy hi1 hi2 => by rw [frameKey'_eq]; exact hK y i hy hi1 hi2,
    frameWindow_of_frameKey'_eq_obs_from h hnc hf (hend.le.trans hTb) ?_⟩
  intro y z i m hy hz' hi1 hi2 hm1 hm2
  rw [hK y i hy hi1 hi2, hK z m hz' hm1 hm2]

end FrameWindowLeaf

/-! ## Proposal membership and leaf 5, the round crossing -/

section RoundCross

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

open SA (gbar)
open Healing.Growing (NoRestartAfter)

/-- An honestly signed row is processed strictly before a sufficiently late honest proposal,
even if the signer has been compromised by then, under the signed-row service clause
(`Service.signedRow`, `Healing.Growing.ResetService.signedRow`). -/
theorem rows_delivered_service_at_from {g ΔF b v : Time}
    (hrows : ∀ x i att, x ∈ H (tr.time i) → tr.SignAt x i att →
      ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
        tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
        ∃ k ≤ j, tr.ProcessAttAt y k att ∧
          tr.time k < tr.deadline y k (max (tr.time i) g) ΔF)
    (hnr : NoRestartAfter tr H (gbar g))
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hv : gbar g ≤ v) {p : Fin P.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    {X : A.Blk} (hX : tr.ProposesAt p kX X)
    (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b) {y : Fin P.n} {k : Nat}
    (hy : y ∈ H (tr.time k)) {att : FG.Att P.n} (hsig : tr.SignAt y k att)
    (hk : tr.time k ≤ v) : ∃ k' < kX, tr.ProcessAttAt p k' att := by
  have hdl0 : ∀ j ≤ kX, ∀ τ : Time,
      tr.deadline p j τ ΔF ≤ max τ (gbar g) + ΔF := fun j hj τ =>
    Compose.deadline_le_of_restarts
      (fun k' hk' hr => hnr p k' (hrun.antitone (hrun.time_mono (hk'.trans hj)) hp) hr) τ ΔF
  have hg : max (tr.time k) g ≤ v := max_le hk ((Healing.le_gbar g).trans hv)
  have hdl : ∀ j ≤ kX,
      tr.deadline p j (max (tr.time k) g) ΔF ≤ v + ΔF := by
    intro j hj
    have := hdl0 j hj (max (tr.time k) g)
    have := max_le hg hv
    linarith
  obtain ⟨acc, hcall⟩ := hX.1.1
  obtain ⟨k', hk', hproc, hlt⟩ := hrows y k att hy hsig p kX hp
    ⟨_, hcall⟩ hkb (by linarith [hdl kX le_rfl])
  refine ⟨k', lt_of_le_of_ne hk' fun h => ?_, hproc⟩
  subst h
  linarith only [hdl k' le_rfl, hlt, hvx]

/-- A proposal's immediate acceptance is held while its proposer is honest, for a run from starts
`ini` at which the AC meets the requirements, with the genesis root: the middle component of
`Healing.accept_of_proposesAt_from` on the proposer's prefix. -/
theorem proposal_mem_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hq : ∀ y, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg)
    (hnc : Compose.NoCollRun dg tr) {p : Fin P.n} {k : Nat}
    (hp : p ∈ H (tr.time k)) {B : A.Blk}
    (hB : tr.ProposesAt p k B) : B ∈ (tr.state p (k + 1)).fg.tree := by
  have hr := hrun.upTo (hrun.time_nonneg k)
  have hB' : (tr.upTo (tr.time k)).ProposesAt p k B :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hB.1⟩, hB.2.1, hB.2.2⟩
  have hm := (Healing.accept_of_proposesAt_from hr hroot (hnc.upTo _) hp (hq p) hB').2.1
  rwa [Trace.upTo_state tr p (fun q hq => hrun.time_mono (by omega))] at hm

/-- Leaf 5: delivered historical rows cross one height; honesty is read separately at every cut.
For a run from starts `ini` at which the AC meets the requirements, with the genesis root and the
signed-row service clause (`Service.signedRow`). -/
theorem round_cross_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hq : ∀ y, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b v : Time}
    (hrows : ∀ x i att, x ∈ H (tr.time i) → tr.SignAt x i att →
      ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
        tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
        ∃ k ≤ j, tr.ProcessAttAt y k att ∧
          tr.time k < tr.deadline y k (max (tr.time i) g) ΔF)
    (hnr : NoRestartAfter tr H (gbar g))
    {B D X : A.Blk} (hBH : B ∈ tr.HonestBlocksAt H)
    (hBD : Anc (tr.HonestBlocksAt H) B D) (hpar : X.parent = some D.root)
    {p : Fin P.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    (hX : tr.ProposesAt p kX X) (hf : 3 * (H (tr.time kX))ᶜ.ncard ≤ P.n - 1)
    (hv : gbar g ≤ v) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hage : B.slot + P.δt ≤ X.slot)
    (hrow : ∀ y ∈ H (tr.time kX),
      (∃ w c, w ∈ H (tr.time c) ∧ B ∈ (tr.state w c).fg.tree ∧
        ∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧
          tr.time k ≤ v ∧ att.h = ((tr.state w c).fg.σ B.root).h ∧
          att.T = ((tr.state w c).fg.σ B.root).Th) ∨
      ∃ R, Anc (tr.HonestBlocksAt H) R D ∧ ∃ w c, w ∈ H (tr.time c) ∧
        B ∈ (tr.state w c).fg.tree ∧ R ∈ (tr.state w c).fg.tree ∧
          ((tr.state w c).fg.σ B.root).h < ((tr.state w c).fg.σ R.root).h) :
    B ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ B.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h := by
  classical
  have hage' : B.slot + P.fg.δt ≤ X.slot := hage
  have hd := hrun.time_nonneg kX
  have hle : ∀ q < kX, tr.time q ≤ tr.time kX := fun q hq => hrun.time_mono hq.le
  have hle1 : ∀ q < kX + 1, tr.time q ≤ tr.time kX := fun q hq =>
    hrun.time_mono (by omega)
  have hs := Trace.upTo_state tr p hle
  have hs1 := Trace.upTo_state tr p hle1
  -- Restrict only the proposer's local execution; historical witnesses remain in the full trace.
  have hr := hrun.upTo hd
  have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  have hcoh := Compose.Growing.honest_blocks_coherent_local hrun hnc
  obtain ⟨Pr, hpar', hPr⟩ :=
    Healing.proposal_parent_held_from hr hroot (hnc.upTo _) hp (hq p) hX'
  rw [hs] at hPr
  obtain ⟨-, hXm, he⟩ := Healing.accept_of_proposesAt_from hr hroot (hnc.upTo _) hp (hq p) hX'
  rw [hs1] at hXm he
  have hPrH : Pr ∈ tr.HonestBlocksAt H := ⟨p, kX, _, hd, hle, hp, hPr⟩
  have hDH : D ∈ tr.HonestBlocksAt H := by
    rcases Relation.ReflTransGen.cases_tail hBD with rfl | ⟨Z, -, hZ⟩
    · exact hBH
    · exact hZ.2.1
  obtain rfl : D = Pr := hcoh.1 hDH hPrH (Option.some_injective _ (hpar.symm.trans hpar'))
  have hR := fg_reachable_at_from hrun hd hle hp
  have hR1 := fg_reachable_at_from hrun hd hle1 hp
  have hBDs := store_anc_of_honest_anc_at_from hrun hnc hd hle hp hBD hPr
  have hBst : B ∈ (tr.state p kX).fg.tree := by
    by_cases he : B = D
    · exact he ▸ hPr
    · exact (Anc.mem hBDs he).1
  have hBDh := Healing.h_le_of_store_anc hR hBDs
  have hmono : (tr.state p kX).fg.tree ⊆ (tr.state p (kX + 1)).fg.tree := by
    simpa only [hs, hs1] using Compose.tree_mono hr hp (Nat.le_succ kX)
  have hDm := hmono hPr
  have hBm := hmono hBst
  have hσB := σ_eq_honest_at_from hrun hnc hd hle hp hd hle1 hp hBst hBm
  have hσD := σ_eq_honest_at_from hrun hnc hd hle hp hd hle1 hp hPr hDm
  have hle' := Healing.h_le_of_store_anc hR1 (.single ⟨hDm, hXm, hpar⟩)
  refine ⟨hBm, hXm, ?_⟩
  rw [← hσB]
  rw [← hσD] at hle'
  by_cases hlt : ((tr.state p kX).fg.σ B.root).h < ((tr.state p kX).fg.σ D.root).h
  · omega
  have hDh : ((tr.state p kX).fg.σ D.root).h = ((tr.state p kX).fg.σ B.root).h := by omega
  have hDTh := Healing.Th_eq_of_anc hR hBDs hDh
  have hThS : ((tr.state p kX).fg.σ D.root).ThSlot ≤ B.slot := by
    rw [Healing.ThSlot_eq_of_anc hR hBDs hDh]
    exact Healing.ThSlot_le_slot hR hBst
  let S := Finset.univ.filter (· ∈ H (tr.time kX))
  have hScard : P.fg.q ≤ S.card := by
    have hcard : S.card = (H (tr.time kX)).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp [S]
    rw [hcard]
    have hn : (H (tr.time kX)).ncard + (H (tr.time kX))ᶜ.ncard = P.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    change (2 * P.n + 2) / 3 ≤ _
    omega
  obtain ⟨hfg, hXt, hDt, hσX, hσD', hplace⟩ :=
    Healing.proposal_rows_placed_from hr (fun y _ => hq y) hroot (hnc.upTo _) hp hX' hpar
      (by rwa [hs])
  have hcross := Healing.cross_step hfg hp hXt hDt hpar S hScard ?_ ?_
  · have h1 := hcross.1
    rw [← hσX, he, ← hσD', hs] at h1
    omega
  · intro y hyS
    have hy : y ∈ H (tr.time kX) := (Finset.mem_filter.1 hyS).2
    rcases hrow y hy with ⟨w, c, hw, hBw, k, att, hyk, hsig, hk, hah, haT⟩ |
      ⟨R, hRD, w, c, hw, hBw, hRw, hhR⟩
    · have hσ := σ_eq_honest_at_from hrun hnc (hrun.time_nonneg c)
        (fun q hq => hrun.time_mono hq.le) hw hd hle hp hBw hBst
      rw [hσ] at hah haT
      have hproc := rows_delivered_service_at_from hrows hnr hrun hv hp hX hvx hkb hyk hsig hk
      have hval := Healing.signAt_val (hrun.upTo (hrun.time_nonneg k)) hyk
        ((RunTrace.upTo_signAt _).mpr ⟨le_rfl, hsig⟩)
      rw [← hσD', hs]
      refine ⟨att, hval, hah.trans hDh.symm, haT.trans hDTh.symm, ?_⟩
      exact hplace att (by
        obtain ⟨j, hj, hproc⟩ := hproc
        exact ⟨j, hj, (RunTrace.upTo_processAttAt _).mpr ⟨hrun.time_mono hj.le, hproc⟩⟩)
        (by rw [hs]; exact hah.trans hDh.symm)
        (by rw [hs]; exact haT.trans hDTh.symm)
    · exfalso
      have hRDs := store_anc_of_honest_anc_at_from hrun hnc hd hle hp hRD hPr
      have hRst : R ∈ (tr.state p kX).fg.tree := by
        by_cases he : R = D
        · exact he ▸ hPr
        · exact (Anc.mem hRDs he).1
      have hRDh := Healing.h_le_of_store_anc hR hRDs
      rw [σ_eq_honest_at_from hrun hnc (hrun.time_nonneg c)
          (fun q hq => hrun.time_mono hq.le) hw hd hle hp hBw hBst,
        σ_eq_honest_at_from hrun hnc (hrun.time_nonneg c)
          (fun q hq => hrun.time_mono hq.le) hw hd hle hp hRw hRst] at hhR
      omega
  · rw [← hσD', hs]
    omega

end RoundCross

/-! ## Leaf 14 -/

section HighEntry

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- Leaf 14: two self-entries of equal height, each read at its own observation honest at a time
after its cuts, below two compatible honest blocks, are the same block. The generic leaf supplies
the compatibility of its high origins by `ACHealing.origins_comparable`. -/
theorem high_entry_eq_at_from
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {B B' Z₁ Z₂ : A.Blk}
    (hBB' : Compatible (tr.HonestBlocksAt H) B B')
    (h₁ : Anc (tr.HonestBlocksAt H) Z₁ B) (h₂ : Anc (tr.HonestBlocksAt H) Z₂ B')
    {y₁ y₂ : Fin P.n} {m₁ m₂ : Nat} {t₁ t₂ : Time}
    (ht₁ : 0 ≤ t₁) (hle₁ : ∀ q < m₁, tr.time q ≤ t₁) (hy₁ : y₁ ∈ H t₁)
    (ht₂ : 0 ≤ t₂) (hle₂ : ∀ q < m₂, tr.time q ≤ t₂) (hy₂ : y₂ ∈ H t₂)
    (hZ₁ : Z₁ ∈ (tr.state y₁ m₁).fg.tree) (hZ₂ : Z₂ ∈ (tr.state y₂ m₂).fg.tree)
    (hh : ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have hU := Compose.Growing.honest_blocks_coherent_local h hnc
  -- Both entries below one block `D` held at an honest observation: compare them in that store.
  have key : ∀ {D : A.Blk}, D ∈ tr.HonestBlocksAt H → Anc (tr.HonestBlocksAt H) Z₁ D →
      Anc (tr.HonestBlocksAt H) Z₂ D → Z₁.root = Z₂.root := by
    rintro D ⟨w, k, t, ht, hle, hw, hD⟩ hZ₁D hZ₂D
    have hr := fg_reachable_at_from h ht hle hw
    have mem : ∀ {Z : A.Blk}, Anc (tr.HonestBlocksAt H) Z D → Z ∈ (tr.state w k).fg.tree := by
      intro Z hZ
      by_cases he : Z = D
      · exact he ▸ hD
      · exact (Anc.mem (store_anc_of_honest_anc_at_from h hnc ht hle hw hZ hD) he).1
    have e₁ := σ_eq_honest_at_from h hnc ht₁ hle₁ hy₁ ht hle hw hZ₁ (mem hZ₁D)
    have e₂ := σ_eq_honest_at_from h hnc ht₂ hle₂ hy₂ ht hle hw hZ₂ (mem hZ₂D)
    rw [e₁] at hh hT₁
    rw [e₂] at hh hT₂
    rcases Anc.total hU hZ₁D hZ₂D with h12 | h21
    · have := Healing.Th_eq_of_anc hr
        (store_anc_of_honest_anc_at_from h hnc ht hle hw h12 (mem hZ₂D)) hh.symm
      rw [← hT₁, ← hT₂, this]
    · have := Healing.Th_eq_of_anc hr
        (store_anc_of_honest_anc_at_from h hnc ht hle hw h21 (mem hZ₁D)) hh
      rw [← hT₁, ← hT₂, this]
  -- The later of the two compatible blocks is held, unless all four blocks coincide.
  have top : ∀ {D D' Y Y' : A.Blk}, Anc (tr.HonestBlocksAt H) D D' →
      Anc (tr.HonestBlocksAt H) Y D → Anc (tr.HonestBlocksAt H) Y' D' →
      (Y = D ∧ D = D' ∧ Y' = D') ∨ D' ∈ tr.HonestBlocksAt H := by
    intro D D' Y Y' hDD' hY hY'
    by_cases e₁ : Y' = D'
    · by_cases e₂ : D = D'
      · by_cases e₃ : Y = D
        · exact Or.inl ⟨e₃, e₂, e₁⟩
        · exact Or.inr (e₂ ▸ (Anc.mem hY e₃).2)
      · exact Or.inr (Anc.mem hDD' e₂).2
    · exact Or.inr (Anc.mem hY' e₁).2
  rcases hBB' with hBB' | hB'B
  · rcases top hBB' h₁ h₂ with ⟨rfl, rfl, rfl⟩ | hB'
    · rfl
    · exact key hB' (h₁.trans hBB') h₂
  · rcases top hB'B h₂ h₁ with ⟨rfl, rfl, rfl⟩ | hB
    · rfl
    · exact key hB h₁ (h₂.trans hB'B)

end HighEntry

/-! ## Leaf 4 -/

section RowOrHigh

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

open Healing (cutZ EntryOf)
open Healing.Growing (HZ)

/-- Parent closure at a held-state observation, for any node run under growing faults from any
starts `ini`. -/
theorem mem_of_honest_anc_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin P.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {B C : A.Blk} (h : Anc (tr.HonestBlocksAt H) B C) (hC : C ∈ (tr.state y k).fg.tree) :
    B ∈ (tr.state y k).fg.tree := by
  by_cases he : B = C
  · exact he ▸ hC
  · exact (Anc.mem (store_anc_of_honest_anc_at_from hrun hnc ht hle hy h hC) he).1

/-- The durable client record only holds signatures made before an honest read. -/
private theorem record_facts_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) :
    Healing.Client.SentOK (tr.state y i).record ∧
    (∀ b ∈ (tr.state y i).record.sent,
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.content = b) ∧
    ∀ h r, (tr.state y i).record.lock h = some r →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r) := by
  have hs := Trace.upTo_state tr y hle
  obtain ⟨hok, hsent, hlock⟩ := Healing.record_facts (hrun.upTo ht) hy i
  rw [hs] at hok hsent hlock
  exact ⟨hok, fun b hb => let ⟨k, hk, a, ha, he⟩ := hsent b hb
    ⟨k, hk, a, ((RunTrace.upTo_signAt tr).mp ha).2, he⟩,
    fun h r hl => let ⟨k, hk, a, ha, he⟩ := hlock h r hl
      ⟨k, hk, a, ((RunTrace.upTo_signAt tr).mp ha).2, he⟩⟩

/-- A store's finalized cache lies below a held block above its justified height. -/
private theorem F_anc_of_hj_lt_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    {B : A.Blk} (hB : B ∈ (tr.state y i).fg.tree)
    (hlt : (tr.state y i).fg.hj < ((tr.state y i).fg.σ B.root).h) :
    (tr.state y i).fg.Anc (tr.state y i).fg.F B :=
  have hR := fg_reachable_at_from hrun ht hle hy
  Healing.Store.F_anc_of_hj_lt_of_safe hR hR (Store.accepted_tree _ _ _ _ hR).2.1 subset_rfl
    subset_rfl hf (held_atts_safe_at_from hrun ht hle hy ht hle hy le_rfl le_rfl) hB hlt

/-- A finality lock cannot be above the node's own justification cache. -/
private theorem hj_ge_of_lock_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * P.fg.q - P.n) {h r : Nat}
    (hl : (tr.state y i).record.lock h = some r) : h ≤ (tr.state y i).fg.hj := by
  have hr := hrun.upTo ht
  have hs := Trace.upTo_state tr y hle
  obtain ⟨k, hk, att, hsa, hfin⟩ := (record_facts_at_from hrun ht hle hy).2.2 h r hl
  have hsa' := (RunTrace.upTo_signAt tr).mpr ⟨hle k hk, hsa⟩
  obtain ⟨B, hB, hBj, -⟩ := Healing.signed_fin_justified hr hy hsa' hfin
  have hsk := Trace.upTo_state tr y (fun q hq => hle q (hq.trans hk))
  rw [hsk] at hB hBj
  have hmono : (tr.state y k).fg.hj ≤ (tr.state y i).fg.hj := by
    simpa only [hs, hsk] using Healing.hj_mono hr hy hk.le
  refine le_trans ?_ hmono
  have hR := fg_reachable_at_from hrun ht (fun q hq => hle q (hq.trans hk)) hy
  by_contra hlt
  have hlt' : (tr.state y k).fg.hj < ((tr.state y k).fg.σ B.root).h := by
    have := Healing.Store.hj_lt_h hR hB
    omega
  have hFB := F_anc_of_hj_lt_at_from hrun ht (fun q hq => hle q (hq.trans hk)) hy hf hB hlt'
  obtain ⟨E, hE, hEr, hEB, -⟩ := Healing.Store.J_entry_of_reachable hR hB
  have hEh := Healing.Store.J_height_le hR hB hE hEr
  have hjmax := (Healing.jMax_iff _).1 (Healing.jMax_of_reachable hR) B hB E hE hEr
  obtain ⟨-, hcoh, -, hgen⟩ := Store.accepted_tree _ _ _ _ hR
  rcases Anc.total hcoh hFB hEB with hFE | hEF
  · have := hjmax hFE
    omega
  · obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj', hBjJ, hBjhj⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
    obtain ⟨E', hE', hEr', -, hEg⟩ := Healing.Store.J_entry_of_reachable hR hBj'
    have hEJ : E'.root = (tr.state y k).fg.J.root := hEr'.trans hBjJ
    have hFh := Healing.h_le_of_store_anc hR hFJ
    rcases hEg with rfl | ⟨hEh', -⟩
    · have he := hcoh.1 hE' hJm hEJ
      rw [← he] at hFJ
      have hFg := Anc.antisymm hcoh hFJ (hgen _ hFm)
      have := hjmax (hFg ▸ hgen E hE)
      omega
    · rw [← hEJ, hEh', hBjhj] at hFh
      have := Healing.h_le_of_store_anc hR hEF
      omega

/-- A lock at the cache's justified height names the cache's justified root. -/
private theorem lock_root_eq_J_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin P.n} {i : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * P.fg.q - P.n) {h r : Nat}
    (hl : (tr.state y i).record.lock h = some r) (hj : (tr.state y i).fg.hj = h) :
    r = (tr.state y i).fg.J.root := by
  have hr := hrun.upTo ht
  have hs := Trace.upTo_state tr y hle
  obtain ⟨k, hk, att, hsa, hfin⟩ := (record_facts_at_from hrun ht hle hy).2.2 h r hl
  obtain ⟨B, hB, hBj, hBJ⟩ := Healing.signed_fin_justified hr hy
    ((RunTrace.upTo_signAt tr).mpr ⟨hle k hk, hsa⟩) hfin
  have hB' := Compose.tree_mono hr hy hk.le hB
  have hlek : ∀ q < k, tr.time q ≤ t := fun q hq => hle q (hq.trans hk)
  have hsk := Trace.upTo_state tr y hlek
  rw [hsk] at hB hBj hBJ
  rw [hs] at hB'
  have hσ := σ_eq_honest_at_from hrun hnc ht hlek hy ht hle hy hB hB'
  rw [hσ] at hBj hBJ
  have hR := fg_reachable_at_from hrun ht hle hy
  obtain ⟨-, -, -, ⟨Bj, hBjt, hBjJ, hBjhj⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  have he := Store.J_eq_of_hj_eq_of_safe hR hR hf
    (held_atts_safe_at_from hrun ht hle hy ht hle hy le_rfl le_rfl) hB' hBjt (by omega)
  exact hBJ.symm.trans (he.trans hBjJ)

/-- No honest advance implies no finality lock at the frontier before the deadline. -/
private theorem lock_none_of_noAdvance_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini) {c T t : Time} {h : Nat}
    (hna : ∀ v k att, v ∈ H (max c (tr.time k)) → tr.SignAt v k att → tr.time k < T → att.h ≤ h)
    {y : Fin P.n} {i : Nat} (ht : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t)
    (hyc : y ∈ H (max c t)) (htT : t < T) : (tr.state y i).record.lock h = none := by
  have hy := hrun.antitone (le_max_right _ _) hyc
  rcases hl : (tr.state y i).record.lock h with _ | r
  · rfl
  obtain ⟨k, hk, att, hs, hfin⟩ := (record_facts_at_from hrun ht hle hy).2.2 h r hl
  have hwf := Healing.signAt_wellFormed_from (hrun.upTo ht) hy
    ((RunTrace.upTo_signAt tr).mpr ⟨hle k hk, hs⟩)
  have hbound := hna y k att (hrun.antitone (max_le_max le_rfl (hle k hk)) hyc) hs
    ((hle k hk).trans_lt htT)
  have := hwf.2 (h, r) (by simp [hfin])
  omega

/-- In kind F the source-height lock is free; in kind J it is free or the entry. -/
private theorem lock_free_or_entry_of_frame_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin P.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ i < k, tr.time i ≤ t) (hy : y ∈ H t)
    (hf : (H t)ᶜ.ncard < 2 * P.fg.q - P.n)
    {C E : A.Blk} {h : Nat}
    (hE : EntryOf (tr.state y k).fg C E h) (hCh : ((tr.state y k).fg.σ C.root).h = h)
    (hkind : (tr.state y k).fg.hj < h ∨
      ((tr.state y k).fg.hj = h ∧ (tr.state y k).fg.Anc (tr.state y k).fg.J C)) :
    (tr.state y k).record.lock h = none ∨ (tr.state y k).record.lock h = some E.root := by
  rcases hkind with hlt | ⟨hj, hJC⟩
  · left
    rcases hl : (tr.state y k).record.lock h with _ | r
    · rfl
    · have := hj_ge_of_lock_at_from hrun ht hle hy hf hl
      omega
  rcases hl : (tr.state y k).record.lock h with _ | r
  · exact Or.inl rfl
  refine Or.inr (congrArg some ?_)
  rw [lock_root_eq_J_at_from hrun hnc ht hle hy hf hl hj]
  have hr := fg_reachable_at_from hrun ht hle hy
  obtain ⟨⟨-, hETh⟩, hEh, hEC⟩ := hE
  obtain ⟨-, hJm, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ := Store.cache_invariants _ _ _ _ hr
  have hJh := Healing.Store.J_height_le hr hBj hJm hBjJ.symm
  have hJCh := Healing.h_le_of_store_anc hr hJC
  obtain ⟨E', hE', hE'r, -, hE'g⟩ := Healing.Store.J_entry_of_reachable hr hBj
  have hE'J : E' = (tr.state y k).fg.J := by
    have h1 : (tr.state y k).fg.blocks E'.root = some E' := hE'
    have h2 : (tr.state y k).fg.blocks (tr.state y k).fg.J.root = some (tr.state y k).fg.J := hJm
    rw [hE'r, hBjJ] at h1
    exact Option.some.inj (h1.symm.trans h2)
  subst hE'J
  have hJTh : ((tr.state y k).fg.σ (tr.state y k).fg.J.root).Th = (tr.state y k).fg.J.root := by
    rcases hE'g with he | ⟨-, hTh⟩
    · have hg : (P.genesisBlock A.genesisPayload).root = P.genesisRoot := rfl
      rw [he, hg, Healing.Store.σ_genesis hr]
      rfl
    · exact hTh
  have hJeq : ((tr.state y k).fg.σ C.root).h =
      ((tr.state y k).fg.σ (tr.state y k).fg.J.root).h := by omega
  have h1 := Healing.Th_eq_of_anc hr hJC hJeq
  have h2 := Healing.Th_eq_of_anc hr hEC (hCh.trans hEh.symm)
  rw [hJTh] at h1
  rw [hETh] at h2
  exact h1.symm.trans h2

/-- Client progress uses only its own prefix, with no global origin invariant. -/
private theorem client_progress_of_lock_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {k : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ i < k, tr.time i ≤ t) (hkt : tr.time k ≤ t) (hy : y ∈ H t)
    {C : A.Blk} {signed : Option (FG.Att P.n)}
    (hc : tr.CallAt y k (.fg (.attest C signed)))
    {E : A.Blk} {h : Nat}
    (hE : EntryOf (tr.state y k).fg C E h) (hCh : ((tr.state y k).fg.σ C.root).h = h)
    (hlock : (tr.state y k).record.lock h = none ∨ (tr.state y k).record.lock h = some E.root) :
    (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
      ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root := by
  have hs := Trace.upTo_state tr y hle
  have hE' : EntryOf ((tr.upTo t).state y k).fg C E h := by rwa [hs]
  have hCh' : (((tr.upTo t).state y k).fg.σ C.root).h = h := by rwa [hs]
  have hl' : ((tr.upTo t).state y k).record.lock h = none ∨
      ((tr.upTo t).state y k).record.lock h = some E.root := by rwa [hs]
  rcases Healing.client_progress_of_lock (hrun.upTo ht) hy
      ((Trace.upTo_callAt tr).mpr ⟨hkt, hc⟩) hE' hCh' hl' with hnow | ⟨j, hj, a, ha, hh, hT⟩
  · exact Or.inl hnow
  · exact Or.inr ⟨j, hj, a, ((RunTrace.upTo_signAt tr).mp ha).2, hh, hT⟩

/-- Leaf 4: a held report by a reporter honest at it and at `c_z`, before any height advance and
under the fault bound, either supplies a row of the lower block signed while honest, or is strictly
higher than it. -/
theorem row_or_high_of_report_at_from
    (hrun : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    (hnc : Compose.NoCollRun dg tr) {g T : Time}
    (hf : ∀ t, 0 ≤ t → t < T → 3 * (H t)ᶜ.ncard ≤ P.n - 1) (hna : NoAdvance tr H g T)
    {y : Fin P.n} {i : Nat} {R B : A.Blk} (hyz : y ∈ H (max (cutZ P g) (tr.time i)))
    (hR : ReportAt tr y i R) (hiT : tr.time i < T) (hRm : R ∈ (tr.state y i).fg.tree)
    (hBR : Anc (tr.HonestBlocksAt H) B R)
    (hkind : ((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ B.root).h →
      ((tr.state y i).fg.σ B.root).h = HZ tr H g ∨
      (tr.state y i).fg.hj < ((tr.state y i).fg.σ B.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ B.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R)) :
    B ∈ (tr.state y i).fg.tree ∧ R ∈ (tr.state y i).fg.tree ∧
      ((∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧ tr.time k ≤ tr.time i ∧
        att.h = ((tr.state y i).fg.σ B.root).h ∧
        att.T = ((tr.state y i).fg.σ B.root).Th) ∨
        ((tr.state y i).fg.σ B.root).h < ((tr.state y i).fg.σ R.root).h) := by
  have hy := hrun.antitone (le_max_right _ _) hyz
  have ht0 := hrun.time_nonneg i
  have hle : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono hk.le
  have hr := hrun.upTo ht0
  have hs := Trace.upTo_state tr y hle
  obtain ⟨ell, hc, hto, hres⟩ := hR
  have hc' : (tr.upTo (tr.time i)).CallAt y i (.ac ell) :=
    (Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩
  have hres' : (A.toFG ((tr.upTo (tr.time i)).state y i).ac ell.frame (tr.time i)).2 =
      some R := by rwa [hs]
  have hBm := mem_of_honest_anc_at_from hrun hnc ht0 hle hy hBR hRm
  have hreach := fg_reachable_at_from hrun ht0 hle hy
  have hBRs := store_anc_of_honest_anc_at_from hrun hnc ht0 hle hy hBR hRm
  have hheight := Healing.h_le_of_store_anc hreach hBRs
  refine ⟨hBm, hRm, ?_⟩
  rcases hheight.lt_or_eq with hlt | heq
  · exact Or.inr hlt
  left
  have hf' : (H (tr.time i))ᶜ.ncard < 2 * P.fg.q - P.n := by
    have hbound := hf (tr.time i) ht0 hiT
    have hn := P.hn
    change (H (tr.time i))ᶜ.ncard < 2 * ((2 * P.n + 2) / 3) - P.n
    omega
  obtain ⟨sg', hatt', ht, hfg'⟩ := Healing.toFG_attest hr hy hc' hto hres'
  have hatt := ((Trace.upTo_callAt tr).mp hatt').2
  have ht' : tr.time (i + 1) = tr.time i := ht
  have hle' : ∀ k < i + 1, tr.time k ≤ tr.time i := fun k hk =>
    hrun.time_mono (Nat.lt_succ_iff.mp hk)
  have hs' := Trace.upTo_state tr y hle'
  have hfg : (tr.state y (i + 1)).fg = (tr.state y i).fg := by
    simpa only [hs, hs'] using hfg'
  obtain ⟨⟨E, hE, hEr, hER, hEh, hETh⟩, -⟩ :=
    Store.entry_state_of_source _ _ _ _ hreach R hRm
  have hEnt : EntryOf (tr.state y (i + 1)).fg R E ((tr.state y i).fg.σ B.root).h := by
    rw [hfg]
    exact ⟨⟨hE, hETh.trans hEr.symm⟩, hEh.trans heq.symm, hER⟩
  have hCh : ((tr.state y (i + 1)).fg.σ R.root).h = ((tr.state y i).fg.σ B.root).h := by
    rw [hfg]
    exact heq.symm
  have hTh : E.root = ((tr.state y i).fg.σ B.root).Th :=
    hEr.trans (Healing.Th_eq_of_anc hreach hBRs heq.symm)
  have hlock : (tr.state y (i + 1)).record.lock ((tr.state y i).fg.σ B.root).h = none ∨
      (tr.state y (i + 1)).record.lock ((tr.state y i).fg.σ B.root).h = some E.root := by
    rcases hkind heq.symm with hHZ | hk
    · rw [hHZ]
      exact Or.inl (lock_none_of_noAdvance_at_from hrun hna ht0 hle' hyz hiT)
    · apply lock_free_or_entry_of_frame_at_from hrun hnc ht0 hle' hy hf' hEnt hCh
      rwa [hfg]
  have hrow := client_progress_of_lock_at_from hrun ht0 hle' ht'.le hy hatt hEnt hCh hlock
  rcases hrow with ⟨att, rfl, hah, haT⟩ | ⟨k, hk, att, hsign, hah, haT⟩
  · exact ⟨i + 1, att, ht'.symm ▸ hy, ⟨R, hatt⟩, ht'.le, hah, haT.trans hTh⟩
  · have hkt := hle' k hk
    exact ⟨k, att, hrun.antitone hkt hy, hsign, hkt, hah, haT.trans hTh⟩

end RowOrHigh

/-! ## Leaves 8 and 9, warm proposals in a frame window -/

section WarmProposal

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

open Healing.Growing (HZ)

/-- An honest proposal below a block held at an honest reader is in the reader's tree, below that
block in the reader's store, with the proposer's replay state after its proposal. -/
private theorem proposal_below_held_at {cm proposer dg H tr}
    (hrun : runs.Run cm proposer dg H tr) (hnc : Compose.NoCollRun dg tr) {z : Fin P.n}
    {kB : Nat} {B : A.Blk} (hz : z ∈ H (tr.time kB)) (hB : tr.ProposesAt z kB B) {y : Fin P.n}
    {i : Nat} {R : A.Blk} (hy : y ∈ H (tr.time i)) (hBR : Anc (tr.HonestBlocksAt H) B R)
    (hR : R ∈ (tr.state y i).fg.tree) :
    B ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc B R ∧
      (tr.state z (kB + 1)).fg.σ B.root = (tr.state y i).fg.σ B.root := by
  have hrl := runs.run_local hrun
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrl.time_mono hq.le
  have hi0 := hrl.time_nonneg i
  have hBm := proposal_mem_at_from hrl (runs.run_requirements hrun) (runs.run_root hrun) hnc hz hB
  have hBy := mem_of_honest_anc_at_from hrl hnc hi0 hle hy hBR hR
  exact ⟨hBy, store_anc_of_honest_anc_at_from hrl hnc hi0 hle hy hBR hR,
    σ_eq_honest_at_from hrl hnc (hrl.time_nonneg kB) (fun q hq => hrl.time_mono (by omega)) hz
      hi0 hle hy hBm hBy⟩

/-- Leaf 8: a warm proposal at a constant merged key `v ≥ 2HZ` is at most `r(v)` rounds below
`HZ + 1`. The supplier's `proposal_floor` puts it at or above the window floor, and the proposer's
store has `HZ + 1 ≤ floor + r(v)` (`Healing.le_floor_add_riseRounds`). -/
theorem rounds_le_warm_proposal_at_of_healing (O : ACHealing A sg runs) :
    rounds_le_warm_proposal_at A sg O := by
  intro cm proposer dg H tr g af len u floor v kindJ J B z kB hrun hnc hwin hK hv hlo hhi hz
    hdes hB hBs hf
  have hfl := O.proposal_floor hrun hnc hwin hz hdes hB hBs hlo hhi hf
  have hrl := runs.run_local hrun
  have ht : tr.time kB = P.slotTime u := by rw [hB.2.2, hBs]
  have hzk : z ∈ H (tr.time kB) := ht ▸ hz
  have hkey := hK z kB hzk (ht ▸ hlo) (ht ▸ hhi)
  have hpos := Healing.Store.hj_lt_hmax_of_reachable
    (fg_reachable_at_from hrl (hrl.time_nonneg kB) (fun q hq => hrl.time_mono hq.le) hzk)
  rw [frameKey'_eq] at hkey
  have h := Healing.le_floor_add_riseRounds (tr.state z kB).fg (by omega) (HZ := HZ tr H g)
    (by rw [hkey]; exact hv)
  rw [hkey, hwin.floor_eq z kB hzk (ht ▸ hlo) (ht ▸ hhi)] at h
  have hrr : riseRounds (HZ tr H g) v = Healing.riseRounds (HZ tr H g) v := by
    rw [Healing.riseRounds_eq]
    rfl
  rw [hrr]
  omega

/-- Leaf 9: a report in the window at the height of a warm honest proposal below it is above the
reader's `h_j`, or at it with `J` below the report. The supplier's `proposal_floor`, read in the
reader's store, puts the report at or above the head-height floor; the root kind and
`ACHealing.report_in_frame` decide the case. -/
theorem report_kind_of_warm_at_of_healing (O : ACHealing A sg runs) :
    report_kind_of_warm_at A sg O := by
  intro cm proposer dg H tr lo hi floor u kindJ J B R z kB y i hrun hnc hframe hz hdes hB hBs
    hlo hhi hf hy hR hBR hil hih heq
  have hrl := runs.run_local hrun
  have hfl := O.proposal_floor hrun hnc hframe hz hdes hB hBs hlo hhi hf
  have ht : tr.time kB = P.slotTime u := by rw [hB.2.2, hBs]
  obtain ⟨hRm, hroot⟩ := O.report_in_frame hrun hy hR
  obtain ⟨-, -, hσ⟩ := proposal_below_held_at hrun hnc (ht ▸ hz) hB hy hBR hRm
  rw [hσ] at hfl
  have hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ R.root).h := by
    rw [hframe.floor_eq y i hy hil hih, heq]
    exact hfl
  have hj := Healing.Store.hj_lt_hmax_of_reachable
    (fg_reachable_at_from hrl (hrl.time_nonneg i) (fun q hq => hrl.time_mono hq.le) hy)
  rw [← heq]
  by_cases hc : (tr.state y i).fg.Contest
  · have he := hc.1
    rw [Store.headHeightFloor, ite_eq_left hc] at hfloor
    exact Or.inl (by omega)
  · rw [Store.headHeightFloor, ite_eq_right hc] at hfloor
    by_cases he : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1
    · have hr' : (tr.state y i).fg.fcRoot = (tr.state y i).fg.J := ite_eq_left ⟨he, hc⟩
      rw [hr'] at hroot
      by_cases hlt : (tr.state y i).fg.hj < ((tr.state y i).fg.σ R.root).h
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, hroot⟩
    · exact Or.inl (by omega)

end WarmProposal

/-! ## Leaf 10 -/

section HighProposal

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

open Healing (cutZ)

/-- The fault bound up to the horizon gives fewer than `q` faulty nodes there. -/
theorem faults_lt_q {H : Time → Set (Fin P.n)} {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) {t : Time} (ht : 0 ≤ t)
    (htb : t ≤ b) : (H t)ᶜ.ncard < P.fg.q := by
  have h3 := hf t ht htb
  have hn := P.hn
  change _ < (2 * P.n + 2) / 3
  omega

/-- Leaf 10: a warm high honest proposal forces a reset by the next slot's report deadline. The
leaf's premises are `Premises`; `ACHealing.report_follow` gives a report above the proposal by an
observer honest at the horizon, which is honest at `c_z` and at the report, and the report is at
least as high as the proposal in the reader's store; leaf 6 gives the reset. -/
theorem reset_of_high_proposal_at_of_healing (O : ACHealing A sg runs) :
    reset_of_high_proposal_at A sg O := by
  intro cm proposer dg H tr βK g ΔF b s₀ u N floor kindJ J B z kB hβ hcom hframe hrun hnc hsvc
    hawake hf hcatch hnr hsl htd hsnap hm hs₀ hwarm hN hmb hH hz hdes hB hBs hh
  have hrl := runs.run_local hrun
  have hΔ := P.hΔ
  obtain ⟨y, hy⟩ := hH
  have hP : Premises tr H cm βK proposer dg sg g ΔF b :=
    ⟨hcom, hnc, hsvc, hawake, hf, hcatch, hnr, htd, hsl, hsnap, ⟨y, hy⟩⟩
  have hu1N : P.slotTime (u + 1) ≤ P.slotTime N := P.slotTime_strictMono.monotone hN
  obtain ⟨i, R, hyi, hR, -, hti, hBR, -⟩ := O.report_follow hβ hrun hP hframe hm hwarm hN hmb
    ⟨hz, hdes, hB, hBs⟩ y (hrl.antitone (by linarith) hy)
  have hzk : z ∈ H (tr.time kB) := hrl.antitone (by rw [hB.2.2, hBs]; linarith) hz
  obtain ⟨-, hBRs, hσ⟩ :=
    proposal_below_held_at hrun hnc hzk hB hyi hBR (O.report_in_frame hrun hyi hR).1
  have hBR' := Healing.h_le_of_store_anc
    (fg_reachable_at_from hrl (hrl.time_nonneg i) (fun q hq => hrl.time_mono hq.le) hyi) hBRs
  rw [← hσ] at hBR'
  obtain ⟨k, hk, hkb⟩ := hsnap
  have hmaxb : max (cutZ P g) (tr.time i) ≤ b := max_le (hk.2.le.trans hkb) (by linarith)
  obtain ⟨a, ha, hat⟩ := reset_of_high_report_at_from hrl (hrl.antitone hmaxb hy)
    (faults_lt_q hf ((hrl.time_nonneg i).trans (le_max_right _ _)) hmaxb) hR (hh.trans hBR')
  exact ⟨a, ha, hat.trans hti⟩

end HighProposal

/-! ## Leaf 11 -/

section WarmRound

open Node in
/-- An honest proposal comes from the proposal call just before its block cut, at the same time:
the block's parent is the head of the duty that call returned. For any node run from any starts
`ini`. -/
theorem proposalHead_of_proposesAt {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
    {tr : RunTrace A} {ini : Fin P.n → A.State} (h : Node.LocalRun proposer dg H sg tr ini)
    {p : Fin P.n} (hp : p ∈ H) {kX : Nat} {X : A.Blk} (hX : tr.ProposesAt p kX X) :
    ∃ c < kX, ∃ d, ProposalHeadAt tr p c d ∧ tr.time c = tr.time kX ∧
      X.parent = some d.head.root := by
  obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, -⟩ := hX
  rcases Compose.blockCall_cases h hp hc with hg |
    ⟨j, x, rfl, hg, hpr, d, p', hdp, rfl, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hcs : (exec proposer dg p (tr.state p j) (tr.time (j + 2)) (.tick x)).2 =
      [(acCall p (tr.state p j) (tr.time (j + 2)) .tick).2] ++
        ((acProposal (tickStep proposer dg p (tr.state p j) (tr.time (j + 2)) x .acTick).1
          (tr.time (j + 2))).2.1 ::
          (proposeBlock dg p (acProposal (tickStep proposer dg p (tr.state p j)
            (tr.time (j + 2)) x .acTick).1 (tr.time (j + 2))).1 (tr.time (j + 2)) x d.head p').2) ++
        (tickStep proposer dg p (proposeBlock dg p (acProposal (tickStep proposer dg p
          (tr.state p j) (tr.time (j + 2)) x .acTick).1 (tr.time (j + 2))).1 (tr.time (j + 2)) x
          d.head p').1 (tr.time (j + 2)) x .fgUpdate).2 := by
    simp only [exec, onTick, runSteps, tickSteps, List.foldl_cons, List.foldl_nil,
      List.nil_append]
    have hdp' := hdp
    simp only [tickStep] at hdp'
    simp only [tickStep, ite_eq_left hpr, hdp']
  have hl1 : 1 < (exec proposer dg p (tr.state p j) (tr.time (j + 2)) (.tick x)).2.length := by
    rw [hcs]; simp
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hg.2.1 0 (by omega)
  obtain ⟨hn1, ht1, -, -, hl1'⟩ := hg.2.1 1 hl1
  simp only [hcs, List.cons_append, List.getElem_cons_zero,
    List.getElem_cons_succ, Nat.add_zero] at hl0 hl1' hn0 ht0
  have hc0 : tr.CallAt p j (acCall p (tr.state p j) (tr.time (j + 2)) .tick).2 := ⟨hn0, hl0⟩
  have hs1 : tr.state p (j + 1) =
      (tickStep proposer dg p (tr.state p j) (tr.time (j + 2)) x .acTick).1 := by
    rw [tr.state_succ_of_call hc0]
    obtain ⟨hfr, hst, hfg, hrec⟩ := h.cutLaw p hp j _ hc0
    simp only at hfr hst
    rw [ht0] at hst
    simp only [tickStep, acCall]
    cases hpj : tr.post j
    rw [hpj] at hst hfg hrec
    simp only at hst hfg hrec
    rw [← hfg, ← hrec, hst]
  refine ⟨j + 1, by omega, d, ⟨⟨.proposal, frame (tickStep proposer dg p (tr.state p j)
    (tr.time (j + 2)) x .acTick).1, []⟩, p', ⟨hn1, hl1'⟩, rfl, ?_⟩, ht1, rfl⟩
  rw [hs1, ht1]
  simpa [acProposal] using hdp

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

open SA (gbar)
open Healing (cutZ)

/-- Leaf 11: a later honest proposal `δt` slots after a warm one, before any height advance, is
one height above it in its proposer's store. `ACHealing.report_follow` gives every node honest at
the later proposal a report above the earlier proposal and below the later proposal's parent
(`proposalHead_of_proposesAt`); leaf 4, with leaf 9 for the report kind, makes the report a row of
the earlier proposal or strictly higher, and leaf 5 crosses one height. The report-delivery
spacing `t_{s+1} + 2Δ + ΔF ≤ t_{s+δt}` gives the row deadline and `δt ≥ 2`, so the later proposal
is at or after `c_z`. -/
theorem round_of_warm_at_of_healing (O : ACHealing A sg runs) : round_of_warm_at A sg O := by
  intro cm proposer dg H tr βK g ΔF b T s₀ u x N floor kindJ J B X z kB p kX hβ hcom hframe hrun
    hnc hsvc hawake hf hcatch hnr hsl hrd hsnap hm hs₀u hwarm hfol htd hux hxN hmb hHb hTb hna
    hT hz hdes hB hBs hp hdx hX hXs
  have hrl := runs.run_local hrun
  have hΔ := P.hΔ
  have hdF := hsvc.deltaF
  have hmono := P.slotTime_strictMono.monotone
  have hδ2 : 2 ≤ P.δt := by
    by_contra h1
    have h := hrd 0
    have := hmono (show 0 + P.δt ≤ 0 + 1 by omega)
    linarith
  have hu1N : u + 1 ≤ N := by omega
  have hvx : P.slotTime (u + 1) + 2 * P.Δ + ΔF ≤ P.slotTime x := (hrd u).trans (hmono hux)
  have hczx : cutZ P g ≤ P.slotTime x := by
    have hg := ((slotOfSpec_iff.mp slotOf_spec) P (gbar g) (Healing.gbar_nonneg g)).1
    have hs₀ : P.slotOf (gbar g) + 1 ≤ s₀ := by
      by_contra h
      have := hmono (show s₀ ≤ P.slotOf (gbar g) by omega)
      linarith
    exact hmono (show P.slotOf (gbar g) + 3 ≤ x by omega)
  have hP : Premises tr H cm βK proposer dg sg g ΔF b :=
    ⟨hcom, hnc, hsvc, hawake, hf, hcatch, hnr, htd, hsl, hsnap, hHb⟩
  have htX : tr.time kX = P.slotTime x := by rw [hX.2.2, hXs]
  have htB : tr.time kB = P.slotTime u := by rw [hB.2.2, hBs]
  have hvle : P.slotTime (u + 1) + 2 * P.Δ ≤ tr.time kX := by rw [htX]; linarith
  have hxb : tr.time kX ≤ b := by rw [htX]; linarith [hmono hxN]
  have hfol' := fun y (hy : y ∈ H (tr.time kX)) =>
    O.report_follow hβ hrun hP hframe hm hwarm hu1N hmb ⟨hz, hdes, hB, hBs⟩ y
      (hrl.antitone hvle hy)
  -- The later proposal's parent is the head of its proposal call.
  have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  obtain ⟨c, hckX, d, ⟨ℓ, pay, hcℓ, hcall, hd⟩, htc, hpar⟩ :=
    proposalHead_of_proposesAt (hrl.upTo (hrl.time_nonneg kX)) hp hX'
  have hcs := Trace.upTo_state tr p (i := c) (d := tr.time kX)
    (fun q hq => hrl.time_mono (by omega))
  have htc' : tr.time c = tr.time kX := htc
  have hhead : ProposalHeadAt tr p c d :=
    ⟨ℓ, pay, ((Trace.upTo_callAt tr).mp hcℓ).2, hcall, by rw [← hcs]; exact hd⟩
  have hhx := fun (R : A.Blk) (hRd : ∀ x', u + O.follow ≤ x' → x' ≤ N → ∀ w c d,
      w ∈ H (tr.time c) → ProposalHeadAt tr w c d → tr.time c = P.slotTime x' →
        Anc (tr.HonestBlocksAt H) R d.head) =>
    hRd x (by omega) hxN p c d (htc' ▸ hp) hhead (htc'.trans htX)
  obtain ⟨-, Rp, -, -, -, -, hBRp, hRpd⟩ := hfol' p hp
  -- The earlier proposal is held while its proposer is honest.
  have hzk : z ∈ H (tr.time kB) := hrl.antitone (by rw [htB]; linarith) hz
  have hBH : B ∈ tr.HonestBlocksAt H :=
    ⟨z, kB + 1, tr.time kB, hrl.time_nonneg kB, fun q hq => hrl.time_mono (by omega), hzk,
      proposal_mem_at_from hrl (runs.run_requirements hrun) (runs.run_root hrun) hnc hzk hB⟩
  refine round_cross_at_from hrl (runs.run_requirements hrun) (runs.run_root hrun) hnc
    hsvc.signedRow hnr hBH (hBRp.trans (hhx Rp hRpd)) hpar hp hX
    (hf _ (hrl.time_nonneg kX) hxb) (v := P.slotTime (u + 1) + 2 * P.Δ)
    (by linarith [hmono (show s₀ ≤ u + 1 by omega)]) (by rw [htX]; exact hvx) hxb
    (by rw [hBs, hXs]; exact hux) ?_
  intro y hy
  obtain ⟨i, R, hyi, hR, htil, hti, hBR, hRd⟩ := hfol' y hy
  have hyz : y ∈ H (max (cutZ P g) (tr.time i)) :=
    hrl.antitone (max_le (htX ▸ hczx) (hti.trans hvle)) hy
  have hlo : P.slotTime s₀ ≤ P.slotTime u := hmono hs₀u
  have hhi : P.slotTime u ≤ P.slotTime N + 2 * P.Δ := by linarith [hmono (show u ≤ N by omega)]
  obtain ⟨hBy, hRy, hor⟩ := row_or_high_of_report_at_from hrl hnc
    (fun t ht htT => hf t ht (htT.le.trans hTb)) hna hyz hR (hti.trans_lt hT)
    (O.report_in_frame hrun hyi hR).1 hBR
    (fun heq => Or.inr
      (report_kind_of_warm_at_of_healing O hrun hnc hframe (hrl.antitone (by linarith) hz) hdes
        hB hBs hlo hhi
        (P.fg.faults_lt_quorum_margin
          (hf _ (by linarith [hmono (Nat.zero_le u), P.slotTime_zero]) (by linarith)))
        hyi hR hBR (hlo.trans htil) (by linarith [hmono hu1N]) heq))
  rcases hor with ⟨k, att, hyk, hs, hk, hah, haT⟩ | hh
  · exact Or.inl ⟨y, i, hyi, hBy, k, att, hyk, hs, hk.trans hti, hah, haT⟩
  · exact Or.inr ⟨R, hhx R hRd, y, i, hyi, hBy, hRy, hh⟩

end WarmRound

/-! ## Leaf 12 -/

section HighRowSource

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

open Healing (cutZ)
open Healing.Growing (HZ IsReset)

/-- A high report, by a reader honest at it and at `c_z`, by the horizon of a premised reset, has
a high origin no later (`ACHealing.report_origin`); every entry below the report in the reader's
store is below the origin in the origin's store, with the same replay state. -/
private theorem origin_below_report (O : ACHealing A sg runs) {cm proposer dg H tr} {βK : ℚ}
    {g ΔF a b : Time} (hβ : βK ≤ 1 / 2) (hrun : runs.Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg sg g ΔF b) (hres : IsReset tr H g a) (hab : a ≤ b)
    {y : Fin P.n} {i : Nat} {R E : A.Blk} (hyz : y ∈ H (max (cutZ P g) (tr.time i)))
    (hib : tr.time i ≤ b) (hR : ReportAt tr y i R)
    (hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) (hE : E ∈ (tr.state y i).fg.tree)
    (hER : (tr.state y i).fg.Anc E R) :
    ∃ r ≤ i, ∃ l Og, HighOrigin A sg O tr H g y r l Og ∧ E ∈ (tr.state y r).fg.tree ∧
      (tr.state y r).fg.Anc E Og ∧ (tr.state y r).fg.σ E.root = (tr.state y i).fg.σ E.root := by
  have hl := runs.run_local hrun
  have hnc := hp.noColl
  have hy := hl.antitone (le_max_right _ _) hyz
  have hi0 := hl.time_nonneg i
  have hlei : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hl.time_mono hq.le
  obtain ⟨r, hri, l, Og, -, hO, hOg, hROg⟩ := O.report_origin hβ hrun hp hres hab hy hib hR hh
  have hler : ∀ q < r, tr.time q ≤ tr.time i := fun q hq => hl.time_mono (by omega)
  have hRi := (O.report_in_frame hrun hy hR).1
  have hRr := mem_of_honest_anc_at_from hl hnc hi0 hler hy hROg hOg
  have hσR := σ_eq_honest_at_from hl hnc hi0 hler hy hi0 hlei hy hRr hRi
  have hROgh := Healing.h_le_of_store_anc (fg_reachable_at_from hl hi0 hler hy)
    (store_anc_of_honest_anc_at_from hl hnc hi0 hler hy hROg hOg)
  have hEOg := (honest_anc_of_store_anc_at_from hi0 hlei hy hER).trans hROg
  have hEr := mem_of_honest_anc_at_from hl hnc hi0 hler hy hEOg hOg
  refine ⟨r, hri, l, Og, ⟨hl.antitone (max_le_max le_rfl (hl.time_mono hri)) hyz, hO, ?_⟩, hEr,
    store_anc_of_honest_anc_at_from hl hnc hi0 hler hy hEOg hOg,
    σ_eq_honest_at_from hl hnc hi0 hler hy hi0 hlei hy hEr hE⟩
  rw [hσR] at hROgh
  omega

/-- Leaf 12: a high signing, by a signer honest at it and at `c_z`, by the horizon of a premised
reset, has a high origin strictly before it holding the signed entry. The signing comes from a
report at the same time (leaf 7), whose origin `ACHealing.report_origin` supplies. -/
theorem high_row_source_at_of_healing (O : ACHealing A sg runs) : high_row_source_at A sg O := by
  intro cm proposer dg H tr βK g ΔF a b v d att hβ hrun hp hres hab hvz hdb hs hh
  have hl := runs.run_local hrun
  obtain ⟨i, hid, R, hR, hti, hhR, E, hE, hER, hEr, hEh, hETh⟩ :=
    sign_from_report_at_from hl (runs.run_requirements hrun) (hl.antitone (le_max_right _ _) hvz)
      hs
  obtain ⟨r, hri, l, Og, ho, hEm, hEOg, hσ⟩ := origin_below_report O hβ hrun hp hres hab
    (by rw [hti]; exact hvz) (by rw [hti]; exact hdb) hR (hh.trans hhR) hE hER
  exact ⟨r, by omega, l, Og, ho, E, hEm, hEOg, hEr, by rw [hσ, hEh], by rw [hσ, hETh]⟩

end HighRowSource

/-! ## Leaf 13 -/

section NoHighContest

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

open Healing (cutZ)
open Healing.Growing (HZ IsReset)

/-- A high self-entry, held at an observation honest by the horizon of a premised reset and left
by a held block, lies below a high origin. A held attestation on it by a signer honest at `c_z`
and at the observation (`Healing.honest_att_of_left`) was signed before the cut, from a report
(leaf 7) whose origin holds the entry (`origin_below_report`). -/
private theorem origin_of_left_entry (O : ACHealing A sg runs) {cm proposer dg H tr} {βK : ℚ}
    {g ΔF a b : Time} (hβ : βK ≤ 1 / 2) (hrun : runs.Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg sg g ΔF b) (hres : IsReset tr H g a) (hab : a ≤ b)
    {y : Fin P.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hyt : y ∈ H t) (htb : t ≤ b) (hq : (H (max (cutZ P g) t))ᶜ.ncard < P.fg.q)
    {E C : A.Blk} (hE : E ∈ (tr.state y k).fg.tree)
    (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h)
    (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ v r l Og, HighOrigin A sg O tr H g v r l Og ∧ tr.time r ≤ b ∧
      Anc (tr.HonestBlocksAt H) E Og := by
  have hl := runs.run_local hrun
  have hnc := hp.noColl
  obtain ⟨W, hW, att, hatt, haT, haH⟩ :=
    Healing.honest_att_of_left (fg_reachable_at_from hl ht hle hyt) hq hET hEC hlt
  obtain ⟨d, hdk, hs⟩ := held_att_signed_at_from hl ht hle hyt ⟨W, hW, hatt⟩
    (hl.antitone (le_max_right _ _) haH)
  have hdt := hle d hdk
  obtain ⟨i, -, R, hR, hti, hah, E', hE', hE'R, hE'r, hE'h, -⟩ :=
    sign_from_report_at_from hl (runs.run_requirements hrun)
      (hl.antitone hdt (hl.antitone (le_max_right _ _) haH)) hs
  have hit : tr.time i ≤ t := hti ▸ hdt
  have hvi : att.val ∈ H (tr.time i) := hl.antitone hit (hl.antitone (le_max_right _ _) haH)
  have hi0 := hl.time_nonneg i
  have hlei : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hl.time_mono hq.le
  obtain rfl : E' = E := (Compose.Growing.honest_blocks_coherent_local hl hnc).1
    ⟨att.val, i, tr.time i, hi0, hlei, hvi, hE'⟩ ⟨y, k, t, ht, hle, hyt, hE⟩ (hE'r.trans haT)
  have hσE := σ_eq_honest_at_from hl hnc hi0 hlei hvi ht hle hyt hE' hE
  rw [hσE] at hE'h
  obtain ⟨r, hri, l, Og, ho, -, hEOg, -⟩ := origin_below_report O hβ hrun hp hres hab
    (hl.antitone (max_le_max le_rfl hit) haH) (hit.trans htb) hR (by omega) hE' hE'R
  exact ⟨att.val, r, l, Og, ho, (hl.time_mono hri).trans (hit.trans htb),
    honest_anc_of_store_anc_at_from hi0 (fun q hq => hl.time_mono (by omega)) hvi hEOg⟩

/-- Leaf 13: by the horizon of a premised reset, no honest store contests at `h_max ≥ HZ + 2`.
In a contest, `J` is a self-entry at `h_j ≥ HZ + 1` not below the contested chain `C`; the entry
of `C` at `h_j` is another. Both are left by held blocks, so both lie below high origins
(`origin_of_left_entry`), which `ACHealing.origins_comparable` makes compatible; leaf 14 makes the
two entries equal, so `J` is below `C`. -/
theorem no_high_contest_at_of_healing (O : ACHealing A sg runs) : no_high_contest_at A sg O := by
  intro cm proposer dg H tr βK g ΔF a b p i hβ hrun hp ha hab hpH hib
  rintro ⟨⟨hmj, C, hC, -, hCh, hJC⟩, hmax⟩
  have hrl := runs.run_local hrun
  have ht := hrl.time_nonneg i
  have hi : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrl.time_mono hq.le
  have hU := Compose.Growing.honest_blocks_coherent_local hrl hp.noColl
  have hreach := fg_reachable_at_from hrl ht hi hpH
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨p, i, tr.time i, ht, hi, hpH, h⟩
  have hq : (H (max (cutZ P g) (tr.time i)))ᶜ.ncard < P.fg.q := by
    obtain ⟨j, hj, hjb⟩ := hp.snapshot
    exact faults_lt_q hp.faults (ht.trans (le_max_right _ _)) (max_le (hj.2.le.trans hjb) hib)
  obtain ⟨_, hJm, _, ⟨Bj, hBj, hBjJ, hBjhj⟩, _⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨EJ, hEJ, hEJr, hEJB, hcase⟩ := Healing.Store.J_entry_of_reachable hreach hBj
  obtain rfl : EJ = (tr.state p i).fg.J := hU.1 (hsub hEJ) (hsub hJm) (hEJr.trans hBjJ)
  rcases hcase with hg | ⟨hJh, hJT⟩
  · exact hJC (hg ▸ (Store.accepted_tree _ _ _ _ hreach).2.2.2 C hC)
  have hjlt := Healing.Store.hj_lt_h hreach hBj
  obtain ⟨EC, hEC, hECC, hECh, hECT⟩ := Healing.entry_at_height hreach hC
    (h := (tr.state p i).fg.hj) (by omega) (by omega)
  obtain ⟨v₁, r₁, l₁, B₁, ho₁, hr₁b, hJB₁⟩ := origin_of_left_entry O hβ hrun hp ha hab
    ht hi hpH hib hq hEJ hJT (by omega) hEJB (by omega)
  obtain ⟨v₂, r₂, l₂, B₂, ho₂, hr₂b, hECB₂⟩ := origin_of_left_entry O hβ hrun hp ha hab
    ht hi hpH hib hq hEC hECT (by omega) hECC (by omega)
  have he := high_entry_eq_at_from hrl hp.noColl
    (O.origins_comparable hβ hrun hp ha hab ho₁.1 ho₁.2.1 hr₁b ho₁.2.2 ho₂.1 ho₂.2.1 hr₂b
      ho₂.2.2)
    hJB₁ hECB₂ ht hi hpH ht hi hpH hEJ hEC (by omega) hJT hECT
  have heq : EC = (tr.state p i).fg.J := hU.1 (hsub hEC) (hsub hEJ) he.symm
  exact hJC (heq ▸ hECC)

end NoHighContest

end Consensus.Goldilocks.Generic
