import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Concrete Gaussian reference leaves for v2.tex, lines 88 and 313–320.
The Lebesgue normalizer is proved only after integrability. The complex law is
an actual transport of two independent real Gaussian components. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace NlsGge.Measure

/-- The variance of each real component of the source's proper complex Gaussian. -/
def componentVariance (a : ℝ) : ℝ≥0 := Real.toNNReal (1 / (2 * a))

lemma componentVariance_coe (a : ℝ) (ha : 0 < a) :
    (componentVariance a : ℝ) = 1 / (2 * a) := by
  exact Real.coe_toNNReal _ (by positivity)

/-- Real pair to complex coordinate, with the source's ordinary real Jacobian. -/
theorem complexGaussian_measurable_transport :
    Measurable (Complex.measurableEquivRealProd.symm : (ℝ × ℝ) → ℂ) :=
  Complex.measurableEquivRealProd.symm.measurable

lemma sqNorm_realProd (p : ℝ × ℝ) :
    ‖Complex.measurableEquivRealProd.symm p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [pow_two]

lemma complexGaussianKernel_realProd (a : ℝ) (p : ℝ × ℝ) :
    Real.exp (-a * ‖Complex.measurableEquivRealProd.symm p‖ ^ 2) =
      Real.exp (-a * p.1 ^ 2) * Real.exp (-a * p.2 ^ 2) := by
  rw [sqNorm_realProd, mul_add, Real.exp_add]

/-- Ordinary planar Gaussian integrability; positivity is indispensable. -/
theorem integrable_complexGaussianKernel (a : ℝ) (ha : 0 < a) :
    Integrable (fun z : ℂ => Real.exp (-a * ‖z‖ ^ 2)) := by
  have hp := (integrable_exp_neg_mul_sq ha).mul_prod (integrable_exp_neg_mul_sq ha)
  apply (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding).mp
  rw [Measure.volume_eq_prod]
  simpa only [Function.comp_def, complexGaussianKernel_realProd] using hp

/-- Planar normalizer for ordinary two-dimensional Lebesgue measure. -/
theorem integral_complexGaussianKernel (a : ℝ) (ha : 0 < a) :
    (∫ z : ℂ, Real.exp (-a * ‖z‖ ^ 2)) = Real.pi / a := by
  have _hi := integrable_complexGaussianKernel a ha
  rw [← Complex.volume_preserving_equiv_real_prod.symm.integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  simp_rw [complexGaussianKernel_realProd]
  rw [Measure.volume_eq_prod]
  have hi := (integrable_exp_neg_mul_sq ha).mul_prod (integrable_exp_neg_mul_sq ha)
  rw [integral_prod _ hi]
  simp only [integral_const_mul, integral_mul_const]
  rw [integral_gaussian, ← pow_two]
  exact Real.sq_sqrt (by positivity)

/-- Concrete independent real pair, transported to a complex coordinate. -/
def complexGaussian (a : ℝ) : MeasureTheory.Measure ℂ :=
  ((gaussianReal 0 (componentVariance a)).prod
    (gaussianReal 0 (componentVariance a))).map Complex.measurableEquivRealProd.symm

instance complexGaussian_probability (a : ℝ) : IsProbabilityMeasure (complexGaussian a) := by
  unfold complexGaussian
  infer_instance

lemma componentVariance_ne_zero (a : ℝ) (ha : 0 < a) : componentVariance a ≠ 0 := by
  intro hv
  have hc := componentVariance_coe a ha
  rw [hv, NNReal.coe_zero] at hc
  have hp : (0 : ℝ) < 1 / (2 * a) := by positivity
  linarith

lemma realGaussianPDF_pair (a : ℝ) (ha : 0 < a) (x y : ℝ) :
    gaussianPDFReal 0 (componentVariance a) x * gaussianPDFReal 0 (componentVariance a) y =
      (a / Real.pi) * Real.exp (-a * (x ^ 2 + y ^ 2)) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hp0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hc : 2 * Real.pi * (componentVariance a : ℝ) = Real.pi / a := by
    rw [componentVariance_coe a ha]
    field_simp
    <;> ring
  have he (t : ℝ) : -(t - 0) ^ 2 / (2 * (componentVariance a : ℝ)) = -a * t ^ 2 := by
    rw [componentVariance_coe a ha]
    field_simp
    <;> ring
  have hs : (Real.sqrt (Real.pi / a))⁻¹ * (Real.sqrt (Real.pi / a))⁻¹ = a / Real.pi := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by positivity)]
    field_simp
  simp only [gaussianPDFReal_def, hc, he]
  calc
    _ = ((Real.sqrt (Real.pi / a))⁻¹ * (Real.sqrt (Real.pi / a))⁻¹) *
        (Real.exp (-a * x ^ 2) * Real.exp (-a * y ^ 2)) := by ring
    _ = _ := by rw [hs, ← Real.exp_add, ← mul_add]

/-- The transported independent real pair has exactly the source's planar density. -/
theorem complexGaussian_density (a : ℝ) (ha : 0 < a) :
    complexGaussian a = (volume : MeasureTheory.Measure ℂ).withDensity
      (fun z : ℂ => ENNReal.ofReal ((a / Real.pi) * Real.exp (-a * ‖z‖ ^ 2))) := by
  unfold complexGaussian
  rw [gaussianReal_of_var_ne_zero 0 (componentVariance_ne_zero a ha),
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
  rw [← Measure.volume_eq_prod]
  ext s hs
  rw [Measure.map_apply complexGaussian_measurable_transport hs,
    withDensity_apply _ (complexGaussian_measurable_transport hs),
    withDensity_apply _ hs,
    ← Complex.volume_preserving_equiv_real_prod.symm.setLIntegral_comp_preimage hs
      (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards with p
  simp only [gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), realGaussianPDF_pair a ha,
    sqNorm_realProd]

lemma integrable_realGaussian_sq (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
  simpa only [id_eq] using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq

lemma integral_realGaussian_sq (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have _hi := integrable_realGaussian_sq v
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hv
  simpa only [integral_id_gaussianReal, sub_zero] using hv

/-- Square norm is integrable under the actual complex law. -/
theorem integrable_complexGaussian_sqNorm (a : ℝ) :
    Integrable (fun z : ℂ => ‖z‖ ^ 2) (complexGaussian a) := by
  unfold complexGaussian
  rw [Complex.measurableEquivRealProd.symm.measurableEmbedding.integrable_map_iff]
  have hi := integrable_realGaussian_sq (componentVariance a)
  convert! (hi.comp_fst (gaussianReal 0 (componentVariance a))).add
    (hi.comp_snd (gaussianReal 0 (componentVariance a))) using 1
  funext p
  exact sqNorm_realProd p

/-- Exact mean square, with real component variance 1/(2a), hence total 1/a. -/
theorem integral_complexGaussian_sqNorm (a : ℝ) (ha : 0 < a) :
    (∫ z : ℂ, ‖z‖ ^ 2 ∂complexGaussian a) = 1 / a := by
  have _hi := integrable_complexGaussian_sqNorm a
  unfold complexGaussian
  rw [integral_map complexGaussian_measurable_transport.aemeasurable (by fun_prop)]
  simp_rw [sqNorm_realProd]
  have hi := integrable_realGaussian_sq (componentVariance a)
  rw [integral_add (hi.comp_fst _) (hi.comp_snd _)]
  have hf : (∫ p : ℝ × ℝ, p.1 ^ 2
      ∂(gaussianReal 0 (componentVariance a)).prod (gaussianReal 0 (componentVariance a))) =
      (componentVariance a : ℝ) := by
    rw [integral_prod _ (hi.comp_fst _)]
    simp only [integral_const, probReal_univ, one_smul]
    exact integral_realGaussian_sq _
  have hs : (∫ p : ℝ × ℝ, p.2 ^ 2
      ∂(gaussianReal 0 (componentVariance a)).prod (gaussianReal 0 (componentVariance a))) =
      (componentVariance a : ℝ) := by
    rw [integral_prod_symm _ (hi.comp_snd _)]
    simp only [integral_const, probReal_univ, one_smul]
    exact integral_realGaussian_sq _
  rw [hf, hs, componentVariance_coe a ha]
  field_simp [ne_of_gt ha]
  <;> ring

lemma measurable_normalizedGaussianKernel (a : ℝ) :
    Measurable (fun z : ℂ => (a / Real.pi) * Real.exp (-a * ‖z‖ ^ 2)) := by fun_prop

lemma normalizedGaussianKernel_nonneg (a : ℝ) (ha : 0 < a) (z : ℂ) :
    0 ≤ (a / Real.pi) * Real.exp (-a * ‖z‖ ^ 2) := by positivity

lemma integrable_normalizedGaussianKernel (a : ℝ) (ha : 0 < a) :
    Integrable (fun z : ℂ => (a / Real.pi) * Real.exp (-a * ‖z‖ ^ 2)) :=
  (integrable_complexGaussianKernel a ha).const_mul _

lemma integral_normalizedGaussianKernel (a : ℝ) (ha : 0 < a) :
    (∫ z : ℂ, (a / Real.pi) * Real.exp (-a * ‖z‖ ^ 2)) = 1 := by
  have _hi := integrable_normalizedGaussianKernel a ha
  rw [integral_const_mul, integral_complexGaussianKernel a ha]
  field_simp [ne_of_gt ha, ne_of_gt Real.pi_pos]


theorem measurable_complexNeg : Measurable (fun z : ℂ => -z) := by fun_prop

/-- Centered real-pair construction retains its actual minus-sign law symmetry. -/
theorem complexGaussian_map_neg (a : ℝ) :
    (complexGaussian a).map (fun z : ℂ => -z) = complexGaussian a := by
  have hp :
      ((gaussianReal 0 (componentVariance a)).prod (gaussianReal 0 (componentVariance a))).map
        (Prod.map (fun x : ℝ => -x) (fun y : ℝ => -y)) =
      (gaussianReal 0 (componentVariance a)).prod (gaussianReal 0 (componentVariance a)) := by
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
    simp only [gaussianReal_map_neg, neg_zero]
  have hf :
      (fun z : ℂ => -z) ∘ Complex.measurableEquivRealProd.symm =
        Complex.measurableEquivRealProd.symm ∘
          (Prod.map (fun x : ℝ => -x) (fun y : ℝ => -y)) := by
    funext p
    apply Complex.ext <;> rfl
  unfold complexGaussian
  rw [Measure.map_map measurable_complexNeg complexGaussian_measurable_transport, hf,
    ← Measure.map_map complexGaussian_measurable_transport (by fun_prop), hp]

end NlsGge.Measure
