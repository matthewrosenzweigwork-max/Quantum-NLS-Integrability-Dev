import NlsGge.GK38.GradFundamentalKernels
import NlsGge.GK38.PairPotentialProbe

/-! # K1: independent bilinear constant-kernel probes. -/
set_option autoImplicit false
open Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

/-- Constant vector kernel, with no conjugation of either component. -/
def k1ConstKernel38 (a b : ℂ) : PairKernelCont38 :=
  ContinuousMap.const _ ![a, b]

theorem probe_k1_pairing_const38 (a b c d : ℂ) :
    integralPairCLM38 (k1ConstKernel38 a b) ⟨1, zero_le_one, le_rfl⟩
      (constL2 c, constL2 d) = a * c + b * d := by
  rw [integralPairCLM38_apply]
  unfold pairIntegral38
  have hae : (fun s => pairKernelExt38 (k1ConstKernel38 a b) s 0 *
      potRepFst38 (constL2 c, constL2 d) s +
        pairKernelExt38 (k1ConstKernel38 a b) s 1 * potRepSnd38 (constL2 c, constL2 d) s) =ᵐ[volume]
      fun _ => a * c + b * d := by
    filter_upwards [coverRep38_const_ae c, coverRep38_const_ae d] with s hc hd
    simp [pairKernelExt38, k1ConstKernel38, Set.IccExtend, potRepFst38, potRepSnd38, hc, hd]
  rw [intervalIntegral.integral_congr_ae (by filter_upwards [hae] with s hs _ using hs)]
  simp

/-- An imaginary direction gives the bilinear sign, detecting a Hermitian pairing. -/
theorem probe_k1_pairing_imaginary38 :
    integralPairCLM38 (k1ConstKernel38 Complex.I 0) ⟨1, zero_le_one, le_rfl⟩
      (constL2 Complex.I, constL2 0) = -1 := by
  rw [probe_k1_pairing_const38]
  simp

end
end NlsGge.GK38
