import NlsGge.GK38.GradFundamentalL2Fund
import NlsGge.GK38.GradFundamentalPairingProbe

/-! # K1: normalized constant and internal-cutoff L2 probes. -/
set_option autoImplicit false
open MeasureTheory Set
namespace NlsGge.GK38
noncomputable section

theorem probe_k1_L2_constant38 (a b : ℂ) :
    potNormSq38 (pairKernelL2Class38 (k1ConstKernel38 a b)) = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [potNormSq_pairKernelL2Class38]
  simp [pairKernelExt38, k1ConstKernel38, Set.IccExtend]

theorem probe_k1_L2_cutoff38 (a b : ℂ) (t : Icc (0 : ℝ) 1) :
    potNormSq38 (cutoffPairKernelL2Class38 (k1ConstKernel38 a b) t) =
      (t : ℝ) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  rw [potNormSq_cutoffPairKernelL2Class38]
  have heq : (fun s => ‖cutoffPairKernel38 (k1ConstKernel38 a b) t s 0‖ ^ 2 +
      ‖cutoffPairKernel38 (k1ConstKernel38 a b) t s 1‖ ^ 2) =
      ({s : ℝ | s ≤ (t : ℝ)}.indicator (fun _ => ‖a‖ ^ 2 + ‖b‖ ^ 2)) := by
    funext s
    by_cases hs : s ≤ (t : ℝ)
    · simp [cutoffPairKernel38, pairKernelExt38, k1ConstKernel38, Set.IccExtend, Set.indicator, hs]
    · simp [cutoffPairKernel38, Set.indicator, hs]
  rw [heq, intervalIntegral.integral_indicator t.2]
  simp [mul_add]

/-- The cutoff at an internal time has half the constant kernel's squared mass. -/
theorem probe_k1_L2_half_imaginary38 :
    potNormSq38 (cutoffPairKernelL2Class38 (k1ConstKernel38 Complex.I 0)
      ⟨1 / 2, by norm_num, by norm_num⟩) = 1 / 2 := by
  rw [probe_k1_L2_cutoff38]
  simp

end
end NlsGge.GK38
