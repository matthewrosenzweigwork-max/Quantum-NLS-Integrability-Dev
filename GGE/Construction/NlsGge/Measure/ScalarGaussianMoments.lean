import NlsGge.Measure.ComplexGaussian
import Mathlib.Probability.Distributions.Gaussian.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace NlsGge.Measure

/- The first checked scratch module has no ordinary assigned import path yet.
This private closed witness repeats its exact concrete transport derivation;
it introduces no Gaussian hypothesis. Ordinary integration can use the checked
public theorem once the parent assigns that path. -/
private lemma complexGaussian_gaussian_for_moments (a : ℝ) :
    ProbabilityTheory.IsGaussian (complexGaussian a) := by
  have ht : (Complex.measurableEquivRealProd.symm : (ℝ × ℝ) → ℂ) =
      (Complex.equivRealProdCLM.symm : (ℝ × ℝ) → ℂ) := by
    funext p
    apply Complex.ext <;>
      simp [Complex.measurableEquivRealProd_symm_apply, Complex.equivRealProdCLM_symm_apply]
  unfold complexGaussian
  rw [ht]
  infer_instance

lemma memLp_complexGaussian_realLinear (a : ℝ) (L : ℂ →L[ℝ] ℝ) :
    MemLp L 2 (complexGaussian a) := by
  letI : ProbabilityTheory.IsGaussian (complexGaussian a) :=
    complexGaussian_gaussian_for_moments a
  exact ProbabilityTheory.IsGaussian.memLp_dual (complexGaussian a) L 2 (by simp)

lemma integrable_complexGaussian_realLinear (a : ℝ) (L : ℂ →L[ℝ] ℝ) :
    Integrable L (complexGaussian a) :=
  (memLp_complexGaussian_realLinear a L).integrable (by norm_num)

lemma integrable_complexGaussian_realLinear_sq (a : ℝ) (L : ℂ →L[ℝ] ℝ) :
    Integrable (fun z : ℂ => (L z) ^ 2) (complexGaussian a) :=
  (memLp_complexGaussian_realLinear a L).integrable_sq

lemma integral_complexGaussian_realLinear (a : ℝ) (L : ℂ →L[ℝ] ℝ) :
    (∫ z : ℂ, L z ∂complexGaussian a) = 0 := by
  have _hi := integrable_complexGaussian_realLinear a L
  have hn : (∫ z : ℂ, L z ∂complexGaussian a) =
      -(∫ z : ℂ, L z ∂complexGaussian a) := by
    calc
      _ = ∫ z : ℂ, L z ∂(complexGaussian a).map (fun z : ℂ => -z) := by
        rw [complexGaussian_map_neg]
      _ = ∫ z : ℂ, L (-z) ∂complexGaussian a :=
        integral_map measurable_complexNeg.aemeasurable (by fun_prop)
      _ = -(∫ z : ℂ, L z ∂complexGaussian a) := by
        simp only [map_neg, integral_neg]
  linarith

lemma variance_complexGaussian_realLinear (a : ℝ) (L : ℂ →L[ℝ] ℝ) :
    ProbabilityTheory.variance L (complexGaussian a) =
      (componentVariance a : ℝ) * ((L (1 : ℂ)) ^ 2 + (L Complex.I) ^ 2) := by
  have _hi := integrable_complexGaussian_realLinear_sq a L
  let g : MeasureTheory.Measure ℝ := gaussianReal 0 (componentVariance a)
  let Q : (ℝ × ℝ) →L[ℝ] ℝ :=
    L.comp Complex.equivRealProdCLM.symm.toContinuousLinearMap
  have hleft : MemLp (Q.comp (.inl ℝ ℝ ℝ)) 2 g :=
    ProbabilityTheory.IsGaussian.memLp_dual g (Q.comp (.inl ℝ ℝ ℝ)) 2 (by simp)
  have hright : MemLp (Q.comp (.inr ℝ ℝ ℝ)) 2 g :=
    ProbabilityTheory.IsGaussian.memLp_dual g (Q.comp (.inr ℝ ℝ ℝ)) 2 (by simp)
  have hp : ProbabilityTheory.variance L (complexGaussian a) =
      ProbabilityTheory.variance Q (g.prod g) := by
    unfold complexGaussian
    rw [ProbabilityTheory.variance_map (by fun_prop)
      Complex.measurableEquivRealProd.symm.measurable.aemeasurable]
    rfl
  have hvleft : ProbabilityTheory.variance (Q.comp (.inl ℝ ℝ ℝ)) g =
      (componentVariance a : ℝ) * (L (1 : ℂ)) ^ 2 := by
    change ProbabilityTheory.variance (Q.comp (.inl ℝ ℝ ℝ))
      (gaussianReal 0 (componentVariance a)) = _
    rw [variance_continuousLinearMap_gaussianReal,
      Real.coe_toNNReal _ (sq_nonneg _)]
    change (L (Complex.equivRealProdCLM.symm (1, 0))) ^ 2 *
      (componentVariance a : ℝ) = _
    simp [Complex.equivRealProdCLM_symm_apply, mul_comm]
  have hvright : ProbabilityTheory.variance (Q.comp (.inr ℝ ℝ ℝ)) g =
      (componentVariance a : ℝ) * (L Complex.I) ^ 2 := by
    change ProbabilityTheory.variance (Q.comp (.inr ℝ ℝ ℝ))
      (gaussianReal 0 (componentVariance a)) = _
    rw [variance_continuousLinearMap_gaussianReal,
      Real.coe_toNNReal _ (sq_nonneg _)]
    change (L (Complex.equivRealProdCLM.symm (0, 1))) ^ 2 *
      (componentVariance a : ℝ) = _
    simp [Complex.equivRealProdCLM_symm_apply, mul_comm]
  rw [hp, variance_dual_prod' hleft hright, hvleft, hvright]
  ring

lemma variance_complexGaussian_realLinear_of_pos (a : ℝ) (ha : 0 < a)
    (L : ℂ →L[ℝ] ℝ) :
    ProbabilityTheory.variance L (complexGaussian a) =
      ((L (1 : ℂ)) ^ 2 + (L Complex.I) ^ 2) / (2 * a) := by
  rw [variance_complexGaussian_realLinear, componentVariance_coe a ha]
  ring

lemma integral_complexGaussian_realLinear_sq (a : ℝ) (L : ℂ →L[ℝ] ℝ) :
    (∫ z : ℂ, (L z) ^ 2 ∂complexGaussian a) =
      (componentVariance a : ℝ) * ((L (1 : ℂ)) ^ 2 + (L Complex.I) ^ 2) := by
  have _hi := integrable_complexGaussian_realLinear_sq a L
  exact (ProbabilityTheory.variance_of_integral_eq_zero (by fun_prop)
    (integral_complexGaussian_realLinear a L)).symm.trans
      (variance_complexGaussian_realLinear a L)

lemma integral_complexGaussian_realLinear_sq_of_pos (a : ℝ) (ha : 0 < a)
    (L : ℂ →L[ℝ] ℝ) :
    (∫ z : ℂ, (L z) ^ 2 ∂complexGaussian a) =
      ((L (1 : ℂ)) ^ 2 + (L Complex.I) ^ 2) / (2 * a) := by
  rw [integral_complexGaussian_realLinear_sq, componentVariance_coe a ha]
  ring

end NlsGge.Measure
