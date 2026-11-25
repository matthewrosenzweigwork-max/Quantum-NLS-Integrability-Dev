import Mathlib
import NlsGge.Hierarchy.ALQ4Limit38
import NlsGge.Hierarchy.ALQ4Ensemble38
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALFreeFields38
import NlsGge.Hierarchy.ALPositiveDecompositions38

                                                                                                                                                                                                                                                                                                                                                                                                      
set_option autoImplicit false
open scoped BigOperators Matrix ENNReal
open Set Filter Topology MeasureTheory Metric
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core NlsGge.Pilot
namespace NlsGge.ThirdConsultation.AL
noncomputable section

theorem al077 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁)
    (h2 : 0 < β₂) :
    ∀ s : ℝ, s < 3 / 2 →
      (∀ N : ℕ, IsProbabilityMeasure (alQ4Mu38 s β₀ β₁ β₂ N)) ∧
      IsProbabilityMeasure (alQ4Rho38 s β₀ β₁ β₂) ∧
      (∀ F : BoundedContinuousFunction (SobolevHilbert s) ℝ,
        Tendsto (fun N => ∫ u, F u ∂alQ4Mu38 s β₀ β₁ β₂ N) atTop
          (𝓝 (∫ u, F u ∂alQ4Rho38 s β₀ β₁ β₂)) ∧
        Tendsto (fun N =>
          (∫ g : ℤ → ℂ,
            F (alQ4UhReal38 s β₀ β₁ β₂ N g) *
              alQ4F38 β₀ β₁ β₂ N (alQ4V38 N (alQ4Hat38 β₀ β₁ β₂ N g))
                ∂alFreeLaw38) / alQ4Z38 β₀ β₁ β₂ N) atTop
          (𝓝 ((∫ g : ℤ → ℂ,
            F (alQ4UReal38 s β₀ β₁ β₂ g) *
              Real.exp (-alV2_38 β₁ β₂ (alQ4UReal38 1 β₀ β₁ β₂ g))
                ∂alFreeLaw38) / alQ4Z2_38 β₀ β₁ β₂))) := by
  intro s hs
  refine ⟨fun N => isProbabilityMeasure_alQ4Mu38 h0 h1.le h2.le s N,
    isProbabilityMeasure_alQ4Rho38 h0 h1.le h2 s, fun F => ?_⟩
  have hw := alQ4_weak_tendsto38 h0 h1.le h2 s hs F
  refine ⟨hw, ?_⟩
  have hF : Measurable (fun u : SobolevHilbert s => F u) := F.continuous.measurable
  have hrho := alQ4Rho_integral38 h0 h1.le h2 s (fun u => F u) hF
  rw [hrho] at hw
  rw [show (∫ g : ℤ → ℂ, F (alQ4UReal38 s β₀ β₁ β₂ g) *
      Real.exp (-alV2_38 β₁ β₂ (alQ4UReal38 1 β₀ β₁ β₂ g)) ∂alFreeLaw38) / alQ4Z2_38 β₀ β₁ β₂ =
      (alQ4Z2_38 β₀ β₁ β₂)⁻¹ * ∫ g : ℤ → ℂ, F (alQ4UReal38 s β₀ β₁ β₂ g) *
      Real.exp (-alV2_38 β₁ β₂ (alQ4UReal38 1 β₀ β₁ β₂ g)) ∂alFreeLaw38 from by rw [div_eq_inv_mul]]
  refine hw.congr' ?_
  filter_upwards [alQ4_eventually_good38 h0] with N hN
  rw [alQ4Mu_integral38 h1.le h2.le hN.1 hN.2 s (fun u => F u) hF, div_eq_inv_mul]

end
end NlsGge.ThirdConsultation.AL
