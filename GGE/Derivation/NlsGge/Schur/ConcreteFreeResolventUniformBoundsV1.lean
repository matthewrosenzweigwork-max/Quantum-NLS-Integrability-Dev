import NlsGge.Schur.FreeResolventUniformBoundsPackageAfterScalarSqrtPrerequisite
import NlsGge.Schur.SourcePhysicalFreeResolventRealizationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- Source F:lem:free, with one positive constant chosen before every field,
radius, parity, signed mode and complex spectral parameter. The operators are
built on the actual paired Hilbert space; the imported source realization
proves that the free diagonal is the complementary inverse of the actual
weak-derivative Dirac action. This is a whole-claim candidate pending final
independent source review and canonical integration. -/
theorem concrete_free_resolvent_uniform_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R →
      ∀ (u₁ u₂ : PhysicalL2)
        (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
        (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)),
      ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R → ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R →
      ∀ (n : ℤ), 1 ≤ |(n : ℝ)| → ∀ (z : ℂ) (hz : z ∈ spectralDisk n),
      ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
          ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤ C * R / |(n : ℝ)| ∧
      complexHilbertSchmidtNorm
        (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz) ≤ C * R / |(n : ℝ)| := by
  refine ⟨max (4 * Real.sqrt 2) (2 * Real.sqrt uniformConvolutionConstant), ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity : 0 < 4 * Real.sqrt 2) (le_max_left _ _)
  · intro R hR u₁ u₂ hu₁ hu₂ hball₁ hball₂ n hn z hz
    exact freeResolventPotential_uniform_bounds_on_h1_ball u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz

end NlsGge.Schur
