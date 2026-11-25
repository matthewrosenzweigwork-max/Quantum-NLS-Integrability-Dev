import Mathlib
import NlsGge.ThirdConsultation.M.M032Host
import NlsGge.ThirdConsultation.M.M029Core

/-!
# M-032 support: `potential_tail_energy_ne_top` (proof development, AUTHOR; not self-reviewed)

First conjunct of the M-032 head (`MTwoMode.potentialTailEnergy w φ N ≠ ⊤`), proved for every `N` by domination by
`potentialCoefficientEnergy` (injectivity of `n ↦ 2n` and `n ↦ -2n`, evenness of `w`).  Uses only the landed
`OneDerivativeWeight`, `compEnergy`, `compEnergy_ne_top`, `potentialEnergy_split`.
-/

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem potential_tail_energy_ne_top
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (φ : PotPair)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤) (N : ℕ) :
    MTwoMode.potentialTailEnergy w φ N ≠ ⊤ := by
  classical
  have hev : ∀ k : ℤ, w (-k) = w k := fun k => (NlsGge.ThirdConsultation.M029R.weight_facts w hw k).2
  have h1 : ∑' n : ℤ, ENNReal.ofReal (w (2 * n) ^ 2 * ‖MTwoMode.fourierPotential φ true (2 * n)‖ ^ 2) ≤
      NlsGge.ThirdConsultation.MTwoModeB.compEnergy w φ true := by
    unfold NlsGge.ThirdConsultation.MTwoModeB.compEnergy
    exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℤ => 2 * n)
      (fun a b h => by simpa using h)
      (fun k : ℤ => ENNReal.ofReal (w k ^ 2 * ‖MTwoMode.fourierPotential φ true k‖ ^ 2))
  have h2 : ∑' n : ℤ, ENNReal.ofReal (w (2 * n) ^ 2 * ‖MTwoMode.fourierPotential φ false (-2 * n)‖ ^ 2) ≤
      NlsGge.ThirdConsultation.MTwoModeB.compEnergy w φ false := by
    unfold NlsGge.ThirdConsultation.MTwoModeB.compEnergy
    have e : ∀ n : ℤ, ENNReal.ofReal (w (2 * n) ^ 2 * ‖MTwoMode.fourierPotential φ false (-2 * n)‖ ^ 2) =
        (fun k : ℤ => ENNReal.ofReal (w k ^ 2 * ‖MTwoMode.fourierPotential φ false k‖ ^ 2)) (-2 * n) := by
      intro n
      simp only
      have : (-2 * n : ℤ) = -(2 * n) := by ring
      rw [this, hev]
    rw [tsum_congr e]
    exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℤ => -2 * n)
      (fun a b h => by simpa using h)
      (fun k : ℤ => ENNReal.ofReal (w k ^ 2 * ‖MTwoMode.fourierPotential φ false k‖ ^ 2))
  have hle : MTwoMode.potentialTailEnergy w φ N ≤
      ∑' n : ℤ, (ENNReal.ofReal (w (2 * n) ^ 2 * ‖MTwoMode.fourierPotential φ true (2 * n)‖ ^ 2) +
        ENNReal.ofReal (w (2 * n) ^ 2 * ‖MTwoMode.fourierPotential φ false (-2 * n)‖ ^ 2)) := by
    unfold MTwoMode.potentialTailEnergy
    refine ENNReal.tsum_le_tsum fun n => ?_
    split_ifs
    · rw [← ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)), mul_add]
    · exact zero_le
  rw [ENNReal.tsum_add] at hle
  have htop : NlsGge.ThirdConsultation.MTwoModeB.compEnergy w φ true +
      NlsGge.ThirdConsultation.MTwoModeB.compEnergy w φ false ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨NlsGge.ThirdConsultation.MTwoModeB.compEnergy_ne_top w φ hφ true,
      NlsGge.ThirdConsultation.MTwoModeB.compEnergy_ne_top w φ hφ false⟩
  exact ne_top_of_le_ne_top htop (hle.trans (add_le_add h1 h2))

end NlsGge.ThirdConsultation.M

end
