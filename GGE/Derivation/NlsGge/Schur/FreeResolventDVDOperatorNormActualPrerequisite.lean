import NlsGge.Schur.FreeResolventUniformBoundsPackageAfterScalarSqrtPrerequisite
import NlsGge.Schur.FreeResolventComplexHilbertSchmidtOpNormAfterL2Prerequisites
import NlsGge.Schur.FreeResolventComplementarySquareBoundAfterQDTransport

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

/-- The actual `D V D` free-resolvent block has the operator-norm estimate
deduced from its source-H¹ Hilbert--Schmidt bound. This packages the expensive
Hilbert-space estimate separately from the complementary inverse algebra. -/
theorem freeResolventPotentialFreeResolvent_opNorm_le_actual22
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (R : ℝ) (hR : 1 ≤ R)
    (hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R)
    (hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n) :
    ‖freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz‖ ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
  let DVD : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
  have hpack := freeResolventPotential_uniform_bounds_on_h1_ball
    u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz
  have hDVDhs : complexHilbertSchmidtNorm DVD ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
    change complexHilbertSchmidtNorm DVD ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)|
    exact hpack.2
  have hDVDhsMem : IsComplexHilbertSchmidt DVD := by
    change IsComplexHilbertSchmidt
      (freeResolventPotentialFreeResolventOperator u₁ u₂ hu₁ hu₂ n z hz)
    exact (freeResolventPotentialFreeResolvent_isComplexHilbertSchmidt_from_matrix_energy
      u₁ u₂ hu₁ hu₂ n z hz).1
  have hDVDop : ‖DVD‖ ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
    exact (complexHilbertSchmidt_opNorm_le DVD hDVDhsMem).trans hDVDhs
  simpa only [DVD, freeResolventPotentialFreeResolvent] using hDVDop

end NlsGge.Schur
