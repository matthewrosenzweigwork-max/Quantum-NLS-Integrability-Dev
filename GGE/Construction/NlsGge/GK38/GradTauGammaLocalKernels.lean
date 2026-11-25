import NlsGge.GK38.GradTauGammaKernelContinuity
import NlsGge.GK38.GradTauGammaGammaDerivative
import NlsGge.GK38.GradTauGammaKernelInjective
import NlsGge.GK38.GradTauGammaContourMass

/-! Continuous contour gradients for any genuine isolating family. Derivative
uniqueness and injectivity of the earned L2 pairing restore exact pointwise
selector independence on every closed-unit time. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

def k4aTauContOnCircle38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) (n : ℤ) : PairKernelCont38 :=
  -((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
    circleIntegral (k4aQuotientKernelCont38 φ) (C n) (R n)

def k4aGammaContOnCircle38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) (n : ℤ) : PairKernelCont38 :=
  (-8 * (2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
    circleIntegral (fun z => (z - tauN φ n) • k4aQuotientKernelCont38 φ z) (C n) (R n)

theorem k4aWeightedKernel_circleIntegrable38 (φ : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) (a : ℂ) :
    CircleIntegrable (fun z => (z - a) • k4aQuotientKernelCont38 φ z) (C n) (R n) := by
  have hD := (analyticOnNhd_discrim_z φ).continuousOn.mono (subset_univ (sphere (C n) (R n)))
  have hP := (analyticOnNhd_perChar_z φ).continuousOn.mono (subset_univ (sphere (C n) (R n)))
  have hQ := hD.div hP (isolating_periodic_boundary38 hf n)
  have hQc := hQ.smul (k4aGradDiscrimCont_continuous38 φ).continuousOn
  exact (((continuousOn_id.sub continuousOn_const).smul hQc)).circleIntegrable
    (isolating_radius_pos38 hf n).le

theorem k4aTauContOnCircle_pairing38 (φ : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    k4aKernelPairingMap38 (k4aTauContOnCircle38 φ C R n) = k4aTauCLMOnCircle38 φ C R n := by
  have hi := k4aQuotientKernelCont_circleIntegrable38 φ C R hf n
  change integralPairCLM38 (k4aTauContOnCircle38 φ C R n) ⟨1, zero_le_one, le_rfl⟩ = _
  rw [k4aTauContOnCircle38, k4aIntegralPair_kernel_smul38,
    k4aKernelPairing_circleIntegral38 _ _ _ hi]
  simp only [k4aQuotientKernelCont_pairing38]
  rfl

theorem k4aGammaContOnCircle_pairing38 (φ : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    k4aKernelPairingMap38 (k4aGammaContOnCircle38 φ C R n) = k4aGammaCLMOnCircle38 φ C R n := by
  have hi := k4aWeightedKernel_circleIntegrable38 φ C R hf n (tauN φ n)
  change integralPairCLM38 (k4aGammaContOnCircle38 φ C R n) ⟨1, zero_le_one, le_rfl⟩ = _
  rw [k4aGammaContOnCircle38, k4aIntegralPair_kernel_smul38,
    k4aKernelPairing_circleIntegral38 _ _ _ hi]
  simp only [k4aIntegralPair_kernel_smul38, k4aQuotientKernelCont_pairing38]
  rfl

theorem k4aTauContOnCircle_independent38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C C' : ℤ → ℂ) (R R' : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (hf' : IsolatingFamily38 φ C' R') (n : ℤ) :
    k4aTauContOnCircle38 φ C R n = k4aTauContOnCircle38 φ C' R' n := by
  apply k4aKernelPairingMap_injective38
  rw [k4aTauContOnCircle_pairing38 φ C R hf n, k4aTauContOnCircle_pairing38 φ C' R' hf' n]
  exact k4aTauCLM_circle_independent38 φ hφ C C' R R' hf hf' n

theorem k4aGammaContOnCircle_independent38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C C' : ℤ → ℂ) (R R' : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (hf' : IsolatingFamily38 φ C' R') (n : ℤ) :
    k4aGammaContOnCircle38 φ C R n = k4aGammaContOnCircle38 φ C' R' n := by
  apply k4aKernelPairingMap_injective38
  rw [k4aGammaContOnCircle_pairing38 φ C R hf n, k4aGammaContOnCircle_pairing38 φ C' R' hf' n]
  exact k4aGammaCLM_circle_independent38 φ hφ C C' R R' hf hf' n

def gradGamma2Cont38 (φ : PotPair) (n : ℤ) : PairKernelCont38 :=
  k4aGammaContOnCircle38 φ (discC φ) (discR φ) n

theorem gradGamma2Cont38_apply (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (t : Icc (0 : ℝ) 1) : gradGamma2Cont38 φ n t = gradGamma2_38 φ n t := by
  have hi := k4aWeightedKernel_circleIntegrable38 φ _ _ (isolating_family38 φ hφ) n (tauN φ n)
  change (-8 * (2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
    circleIntegral (fun z => (z - tauN φ n) • k4aQuotientKernelCont38 φ z)
      (discC φ n) (discR φ n) t = _
  rw [k4aKernelEvaluation_circleIntegral38 _ _ _ hi t]
  rfl

theorem hasFDerivAt_gradGamma2Cont38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    HasFDerivAt (fun ψ => gamma2 ψ n)
      (integralPairCLM38 (gradGamma2Cont38 φ n) ⟨1, zero_le_one, le_rfl⟩) φ := by
  change HasFDerivAt _ (k4aKernelPairingMap38 (k4aGammaContOnCircle38 φ (discC φ) (discR φ) n)) φ
  rw [k4aGammaContOnCircle_pairing38 φ _ _ (isolating_family38 φ hφ) n]
  exact k4aGamma_hasFDerivOnAnyCircle38 φ hφ _ _ (isolating_family38 φ hφ) n

end
end NlsGge.GK38
