module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Obligations
import Mathlib.Tactic.Linarith
import ConsensusLean.Lemmas.Tactic.Linarith

public section

namespace Consensus.Goldilocks.Generic

variable {P : Params} {cm : Time → Finset (Fin P.n)}
  {H : Time → Set (Fin P.n)} {g b : Time}

/-- Binding nonemptiness removes the guard on the transported committee count. -/
theorem committeeFaultsUpTo_of_rows {βK : ℚ}
    (hne : ∀ t, 0 ≤ t → (cm t).Nonempty)
    (hc : ∀ t d, max g 0 ≤ t → t ≤ b → 0 ≤ d → d ≤ b → (cm t).Nonempty →
      (((↑(cm t) : Set (Fin P.n)) ∩ (H d)ᶜ).ncard : ℚ) < βK * (cm t).card) :
    CommitteeFaultsUpTo βK cm H g b := by
  intro t d ht hb hd hdb
  have hn := hne t ((le_max_right g 0).trans ht)
  exact ⟨hn, hc t d ht hb hd hdb hn⟩

/-- The admissible committee upper bound supplies the strict half count. -/
theorem committeeFaultsUpTo_of_half {βK : ℚ} (hβK : βK ≤ 1 / 2)
    (h : CommitteeFaultsUpTo βK cm H g b) :
    ∀ t d, max g 0 ≤ t → t ≤ b → 0 ≤ d → d ≤ b →
      (cm t).Nonempty ∧
        2 * ((↑(cm t) : Set (Fin P.n)) ∩ (H d)ᶜ).ncard < (cm t).card := by
  intro t d ht hb hd hdb
  obtain ⟨hne, hf⟩ := h t d ht hb hd hdb
  refine ⟨hne, ?_⟩
  have hbound := hf.trans_le (mul_le_mul_of_nonneg_right hβK
    (by positivity : (0 : ℚ) ≤ (cm t).card))
  have htwo : (2 : ℚ) * ((↑(cm t) ∩ (H d)ᶜ : Set (Fin P.n)).ncard : ℚ) <
      (cm t).card := by linarith
  exact_mod_cast htwo

/-- The population fit supplies the FG's strict-third count in natural form. -/
theorem populationFaults_of_beta {β : ℚ} (hβ : β ≤ 1 / 3)
    (hp : ∀ d, 0 ≤ d → d ≤ b → ((H d)ᶜ.ncard : ℚ) < β * P.n) :
    ∀ d, 0 ≤ d → d ≤ b → 3 * (H d)ᶜ.ncard ≤ P.n - 1 := by
  intro d hd hb
  have hbound := (hp d hd hb).trans_le (mul_le_mul_of_nonneg_right hβ
    (by positivity : (0 : ℚ) ≤ P.n))
  have hthree : (3 : ℚ) * ((H d)ᶜ.ncard : ℚ) < P.n := by linarith
  have hn : 3 * (H d)ᶜ.ncard < P.n := by exact_mod_cast hthree
  omega

end Consensus.Goldilocks.Generic
