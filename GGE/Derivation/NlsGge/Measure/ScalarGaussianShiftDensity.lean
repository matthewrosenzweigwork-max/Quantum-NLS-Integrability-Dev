import NlsGge.Measure.ComplexGaussian

/-! The real scalar likelihood ratio for translating the project's actual
centered Gaussian component. This is the first step toward, but does not
prove, the complex or countable-product translation statements. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace NlsGge.Measure

/-- Translating the actual centered real component by `u` gives its density
relative to the same centered component. The parameter `a` is the project's
source rate, so the component variance remains `1 / (2 * a)`. -/
lemma gaussianReal_map_add_const_withDensity (a u : ℝ) (ha : 0 < a) :
    (gaussianReal 0 (componentVariance a)).map (fun x : ℝ => x + u) =
      (gaussianReal 0 (componentVariance a)).withDensity
        (fun x : ℝ => ENNReal.ofReal (Real.exp (2 * a * u * x - a * u ^ 2))) := by
  let v : ℝ≥0 := componentVariance a
  let likelihood : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Real.exp (2 * a * u * x - a * u ^ 2))
  have hv : v ≠ 0 := componentVariance_ne_zero a ha
  have hvariance : (2 * (v : ℝ))⁻¹ = a := by
    dsimp [v]
    rw [componentVariance_coe a ha]
    field_simp
    <;> ring
  have hpdfReal (x : ℝ) :
      gaussianPDFReal u v x =
        gaussianPDFReal 0 v x * Real.exp (2 * a * u * x - a * u ^ 2) := by
    have hexp :
        -((x - u) ^ 2) / (2 * (v : ℝ)) =
          -(x ^ 2) / (2 * (v : ℝ)) + (2 * a * u * x - a * u ^ 2) := by
      simp only [div_eq_mul_inv, hvariance]
      ring
    simp only [gaussianPDFReal_def, sub_zero]
    rw [hexp, Real.exp_add]
    ring
  have hpdf (x : ℝ) : gaussianPDF u v x = gaussianPDF 0 v x * likelihood x := by
    change ENNReal.ofReal (gaussianPDFReal u v x) =
      ENNReal.ofReal (gaussianPDFReal 0 v x) *
        ENNReal.ofReal (Real.exp (2 * a * u * x - a * u ^ 2))
    rw [hpdfReal x]
    exact ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x)
  have hlikelihood : Measurable likelihood := by
    dsimp [likelihood]
    fun_prop
  change (gaussianReal 0 v).map (fun x : ℝ => x + u) =
    (gaussianReal 0 v).withDensity likelihood
  rw [gaussianReal_map_add_const, zero_add,
    gaussianReal_of_var_ne_zero u hv,
    gaussianReal_of_var_ne_zero 0 hv,
    ← withDensity_mul (volume : Measure ℝ)
      (measurable_gaussianPDF 0 v) hlikelihood]
  congr 1
  funext x
  exact hpdf x

end NlsGge.Measure
