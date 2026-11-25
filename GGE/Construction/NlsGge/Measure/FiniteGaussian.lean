import NlsGge.Measure.ComplexGaussian
import Mathlib.MeasureTheory.Integral.Pi

/-! Concrete finite Gaussian products, including the single zero-mode plane.
These are Gaussian reference leaves, not a finite-gap canonical ensemble theorem. -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure

variable {ι : Type*} [Fintype ι]

/-- The unscaled product of ordinary planar Lebesgue measures. -/
def finiteComplexVolume (ι : Type*) [Fintype ι] : MeasureTheory.Measure (ι → ℂ) :=
  MeasureTheory.Measure.pi (fun _ : ι => (volume : MeasureTheory.Measure ℂ))

/-- Actual finite product of the independently constructed complex Gaussian factors. -/
def finiteComplexGaussian (a : ι → ℝ) : MeasureTheory.Measure (ι → ℂ) :=
  MeasureTheory.Measure.pi (fun i => complexGaussian (a i))

instance finiteComplexGaussian_probability (a : ι → ℝ) :
    IsProbabilityMeasure (finiteComplexGaussian a) := by
  unfold finiteComplexGaussian
  infer_instance

/-- Product kernel integrability is established before its normalizer identity. -/
theorem integrable_finiteComplexGaussianKernel (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    Integrable (fun z : ι → ℂ => ∏ i, Real.exp (-a i * ‖z i‖ ^ 2))
      (finiteComplexVolume ι) := by
  exact Integrable.fintype_prod (fun i => integrable_complexGaussianKernel (a i) (ha i))

/-- Exact finite-plane Gaussian normalizer, with no change of planar volume. -/
theorem integral_finiteComplexGaussianKernel (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ z : ι → ℂ, ∏ i, Real.exp (-a i * ‖z i‖ ^ 2) ∂finiteComplexVolume ι) =
      ∏ i, Real.pi / a i := by
  have _hi := integrable_finiteComplexGaussianKernel a ha
  unfold finiteComplexVolume
  calc
    _ = ∏ i, ∫ z : ℂ, Real.exp (-a i * ‖z‖ ^ 2) := by
      convert! (integral_fintype_prod_eq_prod
        (μ := fun _ : ι => (volume : MeasureTheory.Measure ℂ))
        (fun (i : ι) (z : ℂ) => Real.exp (-a i * ‖z‖ ^ 2))) using 1
    _ = _ := Finset.prod_congr rfl (fun i _ => integral_complexGaussianKernel (a i) (ha i))

/-- Each coordinate has an integrable square norm under the concrete finite product. -/
theorem integrable_finiteComplexGaussian_sqNorm (a : ι → ℝ) (i : ι) :
    Integrable (fun z : ι → ℂ => ‖z i‖ ^ 2) (finiteComplexGaussian a) := by
  unfold finiteComplexGaussian
  convert! (integrable_comp_eval (X := fun _ : ι => ℂ)
    (μ := fun j => complexGaussian (a j)) (i := i)
    (integrable_complexGaussian_sqNorm (a i))) using 1

/-- Each coordinate keeps the exact source variance, including any coordinate labelled zero. -/
theorem integral_finiteComplexGaussian_sqNorm (a : ι → ℝ) (ha : ∀ i, 0 < a i) (i : ι) :
    (∫ z : ι → ℂ, ‖z i‖ ^ 2 ∂finiteComplexGaussian a) = 1 / a i := by
  have hi := integrable_finiteComplexGaussian_sqNorm a i
  unfold finiteComplexGaussian
  calc
    _ = ∫ z : ℂ, ‖z‖ ^ 2 ∂complexGaussian (a i) := by
      convert! (integral_comp_eval (X := fun _ : ι => ℂ)
        (μ := fun j => complexGaussian (a j)) (i := i)
        (integrable_complexGaussian_sqNorm (a i)).aestronglyMeasurable) using 1
    _ = _ := integral_complexGaussian_sqNorm (a i) (ha i)

/-- Zero cutoff still has one Gaussian coordinate rather than an empty product. -/
theorem integral_zeroCutoffGaussian_sqNorm (a : Fin 1 → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ z : Fin 1 → ℂ, ‖z 0‖ ^ 2 ∂finiteComplexGaussian a) = 1 / a 0 :=
  integral_finiteComplexGaussian_sqNorm a ha 0

lemma measurable_finiteGaussianPDF (a : ι → ℝ) :
    Measurable (fun z : ι → ℂ => ∏ i, (a i / Real.pi) * Real.exp (-a i * ‖z i‖ ^ 2)) := by
  fun_prop

lemma integrable_finiteGaussianPDF (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    Integrable (fun z : ι → ℂ => ∏ i, (a i / Real.pi) * Real.exp (-a i * ‖z i‖ ^ 2))
      (finiteComplexVolume ι) := by
  exact Integrable.fintype_prod (fun i => integrable_normalizedGaussianKernel (a i) (ha i))

lemma integral_finiteGaussianPDF (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ z : ι → ℂ, ∏ i, (a i / Real.pi) * Real.exp (-a i * ‖z i‖ ^ 2)
      ∂finiteComplexVolume ι) = 1 := by
  have _hi := integrable_finiteGaussianPDF a ha
  unfold finiteComplexVolume
  calc
    _ = ∏ i, ∫ z : ℂ, (a i / Real.pi) * Real.exp (-a i * ‖z‖ ^ 2) := by
      convert! (integral_fintype_prod_eq_prod
        (μ := fun _ : ι => (volume : MeasureTheory.Measure ℂ))
        (fun (i : ι) (z : ℂ) => (a i / Real.pi) * Real.exp (-a i * ‖z‖ ^ 2))) using 1
    _ = 1 := by simp only [integral_normalizedGaussianKernel _ (ha _), Finset.prod_const_one]

lemma finiteComplexGaussian_density (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    finiteComplexGaussian a = (finiteComplexVolume ι).withDensity
      (fun z : ι → ℂ => ENNReal.ofReal
        (∏ i, (a i / Real.pi) * Real.exp (-a i * ‖z i‖ ^ 2))) := by
  have hi := integrable_finiteGaussianPDF a ha
  unfold finiteComplexVolume at hi
  have hn (z : ι → ℂ) : 0 ≤ ∏ i, (a i / Real.pi) * Real.exp (-a i * ‖z i‖ ^ 2) :=
    Finset.prod_nonneg (fun i _ => normalizedGaussianKernel_nonneg (a i) (ha i) (z i))
  unfold finiteComplexGaussian finiteComplexVolume
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal hi.restrict (Filter.Eventually.of_forall hn),
    Measure.restrict_pi_pi]
  have hp :
      (∫ z : ι → ℂ, ∏ i, (a i / Real.pi) * Real.exp (-a i * ‖z i‖ ^ 2)
        ∂Measure.pi (fun i => (volume : MeasureTheory.Measure ℂ).restrict (s i))) =
      ∏ i, ∫ z : ℂ in s i, (a i / Real.pi) * Real.exp (-a i * ‖z‖ ^ 2) := by
    convert! (integral_fintype_prod_eq_prod
      (μ := fun i : ι => (volume : MeasureTheory.Measure ℂ).restrict (s i))
      (fun (i : ι) (z : ℂ) => (a i / Real.pi) * Real.exp (-a i * ‖z‖ ^ 2))) using 1
  rw [hp, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg (normalizedGaussianKernel_nonneg (a i) (ha i)))]
  apply Finset.prod_congr rfl
  intro i _
  rw [complexGaussian_density (a i) (ha i), withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_normalizedGaussianKernel (a i) (ha i)).restrict
    (Filter.Eventually.of_forall (normalizedGaussianKernel_nonneg (a i) (ha i)))


theorem measurable_finiteComplexNeg :
    Measurable (fun z : ι → ℂ => fun i => -z i) := by fun_prop

/-- Actual finite product law is invariant under simultaneous coordinate minus signs. -/
theorem finiteComplexGaussian_map_neg (a : ι → ℝ) :
    (finiteComplexGaussian a).map (fun z : ι → ℂ => fun i => -z i) =
      finiteComplexGaussian a := by
  unfold finiteComplexGaussian
  have h := Measure.pi_map_pi (μ := fun i : ι => complexGaussian (a i))
    (f := fun (_ : ι) (z : ℂ) => -z)
    (fun _ => measurable_complexNeg.aemeasurable)
  simpa only [complexGaussian_map_neg] using h

end NlsGge.Measure
