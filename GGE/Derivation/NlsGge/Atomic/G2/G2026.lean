import NlsGge.GK38.XiSqKernel
import NlsGge.GK38.TauGammaCoefficient
import NlsGge.GK38.GradEigenDefs

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G2_026 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ gkW ∧
      ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ U,
        (∀ n : ℤ, lamDot φ n-tauN φ n = gamma2 φ n*a5CriticalA38 n φ) ∧
        Summable (fun n : ℤ => ‖a5CriticalA38 n φ‖^2) ∧
        (∑' n : ℤ, ‖a5CriticalA38 n φ‖^2) ≤ C := by
  obtain ⟨V, hV, hVW, B, hB, h⟩ :=
    critical_coefficient_common_l2_bound38 discC discR isolating_selectors_admissible38 φ₀ hφ₀
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV,
    fun φ hφ => hVW (interior_subset hφ), B + 1, by linarith, fun φ hφ => ?_⟩
  have hφV := interior_subset hφ
  obtain ⟨-, hs, hle⟩ := h φ hφV
  exact ⟨fun n => a5CriticalA_identity38 n φ (hVW hφV), hs, by
    have hle' : ∑' n : ℤ, ‖a5CriticalA38 n φ‖ ^ 2 ≤ B := hle
    linarith⟩


end
end NlsGge.GKDefinitionDesign
