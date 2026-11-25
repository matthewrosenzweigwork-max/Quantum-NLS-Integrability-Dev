import NlsGge.Measure.ComplexGaussian
import Mathlib.Probability.Distributions.Gaussian.Basic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Measure

lemma isGaussian_complexGaussian (a : ℝ) :
    ProbabilityTheory.IsGaussian (complexGaussian a) := by
  have ht : (Complex.measurableEquivRealProd.symm : (ℝ × ℝ) → ℂ) =
      (Complex.equivRealProdCLM.symm : (ℝ × ℝ) → ℂ) := by
    funext p
    apply Complex.ext <;>
      simp [Complex.measurableEquivRealProd_symm_apply, Complex.equivRealProdCLM_symm_apply]
  unfold complexGaussian
  rw [ht]
  infer_instance

lemma isGaussian_complexGaussian_realLinear (a : ℝ) (L : ℂ →L[ℝ] ℝ) :
    ProbabilityTheory.IsGaussian ((complexGaussian a).map L) := by
  letI : ProbabilityTheory.IsGaussian (complexGaussian a) := isGaussian_complexGaussian a
  infer_instance

end NlsGge.Measure

