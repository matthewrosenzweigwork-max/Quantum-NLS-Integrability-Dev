import Mathlib
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALSamplingV2Formula38
import NlsGge.Hierarchy.ALQ4Limit38

                                                                                                                                                                                
                                                                                                
                                                                                                
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Analysis
open NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.AL

theorem al070 {β₁ β₂ : ℝ} (h1 : 0 < β₁) (h2 : 0 < β₂) :
    Continuous (alV2_38 β₁ β₂) ∧
    (∀ u : SobolevHilbert 1,
      IntervalIntegrable (fun t : ℝ => ‖alCanon38 u t‖ ^ 4) volume 0 1 ∧
      IntervalIntegrable (fun t : ℝ =>
        2 * ‖alCanon38 u t‖ ^ 6 +
        6 * ‖alCanon38 u t‖ ^ 2 * ‖alDeriv38 u t‖ ^ 2 +
        (2 * (alDeriv38 u t * star (alCanon38 u t)).re) ^ 2) volume 0 1 ∧
      alV2_38 β₁ β₂ u =
        β₁ * (∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 4) +
        β₂ * (∫ t in (0 : ℝ)..1,
          2 * ‖alCanon38 u t‖ ^ 6 +
          6 * ‖alCanon38 u t‖ ^ 2 * ‖alDeriv38 u t‖ ^ 2 +
          (2 * (alDeriv38 u t * star (alCanon38 u t)).re) ^ 2) ∧
      0 ≤ alV2_38 β₁ β₂ u ∧
      0 < Real.exp (-alV2_38 β₁ β₂ u) ∧ Real.exp (-alV2_38 β₁ β₂ u) ≤ 1) := by
  refine ⟨continuous_alV2_38 β₁ β₂, fun u => ?_⟩
  obtain ⟨hi1, hi2, he⟩ := alV2_eq_integral38 β₁ β₂ u
  have hc : ∀ t : ℝ, (alDeriv38 u t * star (alCanon38 u t)).re =
      ((starRingEnd ℂ) (alCanon38 u t) * alDeriv38 u t).re := fun t => by
    rw [mul_comm]; rfl
  have hfun : (fun t : ℝ => 2 * ‖alCanon38 u t‖ ^ 6 +
        6 * ‖alCanon38 u t‖ ^ 2 * ‖alDeriv38 u t‖ ^ 2 +
        (2 * (alDeriv38 u t * star (alCanon38 u t)).re) ^ 2) =
      (fun t : ℝ => 2 * ‖alCanon38 u t‖ ^ 6
        + 6 * ‖alCanon38 u t‖ ^ 2 * ‖alDeriv38 u t‖ ^ 2
        + (2 * ((starRingEnd ℂ) (alCanon38 u t) * alDeriv38 u t).re) ^ 2) := by
    funext t; rw [hc t]
  have hnn := alV2_nonneg38 h1.le h2.le u
  rw [hfun]
  exact ⟨hi1, hi2, he, hnn, Real.exp_pos _, Real.exp_le_one_iff.2 (neg_nonpos.2 hnn)⟩


end NlsGge.ThirdConsultation.AL
