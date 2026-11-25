import NlsGge.GK38.GradFundamentalGradient
import NlsGge.GK38.GradFundamentalL2
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The independent continuous time kernel pairing is itself a bounded linear
map. Its circle-integral interchange is the needed genuine Fubini operation. -/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

theorem k4aIntegralPair_kernel_smul38 (g : PairKernelCont38) (a : ℂ) :
    integralPairCLM38 (a • g) ⟨1, zero_le_one, le_rfl⟩ =
      a • integralPairCLM38 g ⟨1, zero_le_one, le_rfl⟩ := by
  apply ContinuousLinearMap.ext
  intro h
  change pairIntegral38 (a • g) ⟨1, zero_le_one, le_rfl⟩ h =
    a * pairIntegral38 g ⟨1, zero_le_one, le_rfl⟩ h
  unfold pairIntegral38
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
  simp only [pairKernelExt38_of_mem _ hs', ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem k4aIntegralPair_kernel_norm38 (g : PairKernelCont38) :
    ‖integralPairCLM38 g ⟨1, zero_le_one, le_rfl⟩‖ ≤ 2 * ‖g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  exact norm_pairIntegral38_le g ⟨1, zero_le_one, le_rfl⟩ h

def k4aKernelPairingMap38 : PairKernelCont38 →L[ℂ] (PotPair →L[ℂ] ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun g => integralPairCLM38 g ⟨1, zero_le_one, le_rfl⟩
      map_add' := fun g k => integralPairCLM38_kernelAdd g k ⟨1, zero_le_one, le_rfl⟩
      map_smul' := fun a g => k4aIntegralPair_kernel_smul38 g a }
    2 k4aIntegralPair_kernel_norm38

theorem k4aCLM_circleIntegral38 {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (G : ℂ → E) (c : ℂ) (r : ℝ) (hi : CircleIntegrable G c r) :
    L (circleIntegral G c r) = circleIntegral (fun z => L (G z)) c r := by
  unfold circleIntegral
  rw [← L.intervalIntegral_comp_comm hi.out]
  apply intervalIntegral.integral_congr
  intro θ _
  exact L.map_smul (deriv (circleMap c r) θ) (G (circleMap c r θ))

theorem k4aKernelPairing_circleIntegral38 (G : ℂ → PairKernelCont38)
    (c : ℂ) (r : ℝ) (hi : CircleIntegrable G c r) :
    integralPairCLM38 (circleIntegral G c r) ⟨1, zero_le_one, le_rfl⟩ =
      circleIntegral (fun z => integralPairCLM38 (G z) ⟨1, zero_le_one, le_rfl⟩) c r :=
  k4aCLM_circleIntegral38 k4aKernelPairingMap38 G c r hi

theorem k4aKernelEvaluation_circleIntegral38 (G : ℂ → PairKernelCont38)
    (c : ℂ) (r : ℝ) (hi : CircleIntegrable G c r) (t : Icc (0 : ℝ) 1) :
    circleIntegral G c r t = circleIntegral (fun z => G z t) c r :=
  k4aCLM_circleIntegral38 (ContinuousMap.evalCLM ℂ t) G c r hi

end
end NlsGge.GK38
