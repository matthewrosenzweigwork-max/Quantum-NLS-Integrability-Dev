import NlsGge.Measure.ComplexGaussian
import NlsGge.Measure.ScalarGaussianShiftDensity
import NlsGge.Measure.ComplexGaussianShiftExponent

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace NlsGge.Measure

private def scalarShiftDensity (a u x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (2 * a * u * x - a * u ^ 2))

private def pairShiftDensity (a : ℝ) (h : ℂ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  scalarShiftDensity a h.re p.1 * scalarShiftDensity a h.im p.2

private theorem pairShiftDensity_eq_complex (a : ℝ) (h : ℂ) (p : ℝ × ℝ) :
    pairShiftDensity a h p =
      ENNReal.ofReal (Real.exp
        (2 * a * (star h * Complex.measurableEquivRealProd.symm p).re -
          a * ‖h‖ ^ 2)) := by
  dsimp [pairShiftDensity, scalarShiftDensity]
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]
  apply congrArg (fun r : ℝ => ENNReal.ofReal (Real.exp r))
  simpa [Complex.measurableEquivRealProd_symm_apply] using
    (complexGaussianShiftExponent_pair a h p.1 p.2)

/-- Transport a measurable density through a measurable equivalence by the
set-integral change-of-variables formula. -/
private theorem map_withDensity_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e =
      (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs]
  rw [withDensity_apply _ (e.measurable hs)]
  rw [withDensity_apply _ hs]
  symm
  simpa using
    (setLIntegral_map (μ := μ) (f := fun y => f (e.symm y)) (g := e) (s := s)
      hs (hf.comp e.symm.measurable) e.measurable)

/-- The actual proper complex Gaussian, translated by any complex scalar, has
the source-normalized likelihood at the translated output. -/
lemma complexGaussian_map_add_const_withDensity (a : ℝ) (h : ℂ) (ha : 0 < a) :
    (complexGaussian a).map (fun z : ℂ => z + h) =
      (complexGaussian a).withDensity (fun z : ℂ =>
        ENNReal.ofReal (Real.exp
          (2 * a * (star h * z).re - a * ‖h‖ ^ 2))) := by
  let μr : Measure ℝ := gaussianReal 0 (componentVariance a)
  let μpair : Measure (ℝ × ℝ) := μr.prod μr
  let e : ℝ × ℝ ≃ᵐ ℂ := Complex.measurableEquivRealProd.symm
  let pairShift : ℝ × ℝ → ℝ × ℝ :=
    Prod.map (fun x : ℝ => x + h.re) (fun y : ℝ => y + h.im)
  have hpairDensityMeasurable : Measurable (pairShiftDensity a h) := by
    change Measurable (fun p : ℝ × ℝ =>
      scalarShiftDensity a h.re p.1 * scalarShiftDensity a h.im p.2)
    change Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (2 * a * h.re * p.1 - a * h.re ^ 2)) *
        ENNReal.ofReal (Real.exp (2 * a * h.im * p.2 - a * h.im ^ 2)))
    fun_prop
  have hscalarDensityMeasurable (u : ℝ) : Measurable (scalarShiftDensity a u) := by
    change Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (2 * a * u * x - a * u ^ 2)))
    fun_prop
  have hpair :
      μpair.map pairShift = μpair.withDensity (pairShiftDensity a h) := by
    calc
      μpair.map pairShift =
          (μr.map (fun x : ℝ => x + h.re)).prod
            (μr.map (fun y : ℝ => y + h.im)) := by
        change Measure.map
            (Prod.map (fun x : ℝ => x + h.re) (fun y : ℝ => y + h.im))
            ((gaussianReal 0 (componentVariance a)).prod
              (gaussianReal 0 (componentVariance a))) = _
        rw [← Measure.map_prod_map (gaussianReal 0 (componentVariance a))
          (gaussianReal 0 (componentVariance a))
          (by fun_prop) (by fun_prop)]
      _ =
          (μr.withDensity (scalarShiftDensity a h.re)).prod
            (μr.withDensity (scalarShiftDensity a h.im)) := by
        rw [gaussianReal_map_add_const_withDensity a h.re ha,
          gaussianReal_map_add_const_withDensity a h.im ha]
        rfl
      _ = μpair.withDensity (pairShiftDensity a h) := by
        dsimp [μpair]
        rw [prod_withDensity (hscalarDensityMeasurable h.re)
          (hscalarDensityMeasurable h.im)]
        congr 1
  have htranslate (p : ℝ × ℝ) :
      (e p) + h = e (pairShift p) := by
    apply Complex.measurableEquivRealProd.injective
    simp [e, pairShift, Complex.measurableEquivRealProd_apply,
      Complex.measurableEquivRealProd_symm_apply, Complex.add_re, Complex.add_im]
  have hcomposition :
      (fun z : ℂ => z + h) ∘ e = e ∘ pairShift := by
    funext p
    exact htranslate p
  have hmap :
      (μpair.map e).map (fun z : ℂ => z + h) = (μpair.map pairShift).map e := by
    calc
      (μpair.map e).map (fun z : ℂ => z + h) =
          μpair.map ((fun z : ℂ => z + h) ∘ e) := by
        rw [Measure.map_map (by fun_prop) e.measurable]
      _ = μpair.map (e ∘ pairShift) := by rw [hcomposition]
      _ = (μpair.map pairShift).map e := by
        rw [Measure.map_map e.measurable (by fun_prop)]
  have hlikelihood :
      (fun z : ℂ => pairShiftDensity a h (e.symm z)) =
        (fun z : ℂ => ENNReal.ofReal (Real.exp
          (2 * a * (star h * z).re - a * ‖h‖ ^ 2))) := by
    funext z
    simpa [e] using pairShiftDensity_eq_complex a h
      (Complex.measurableEquivRealProd z)
  unfold complexGaussian
  change (μpair.map e).map (fun z : ℂ => z + h) =
    (μpair.map e).withDensity (fun z : ℂ => ENNReal.ofReal (Real.exp
      (2 * a * (star h * z).re - a * ‖h‖ ^ 2)))
  calc
    (μpair.map e).map (fun z : ℂ => z + h) =
        (μpair.map pairShift).map e := hmap
    _ = (μpair.withDensity (pairShiftDensity a h)).map e := by rw [hpair]
    _ = (μpair.map e).withDensity (fun z => pairShiftDensity a h (e.symm z)) :=
      map_withDensity_measurableEquiv e μpair (pairShiftDensity a h)
        hpairDensityMeasurable
    _ = (μpair.map e).withDensity (fun z : ℂ => ENNReal.ofReal (Real.exp
          (2 * a * (star h * z).re - a * ‖h‖ ^ 2))) := by rw [hlikelihood]

end NlsGge.Measure
