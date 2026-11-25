import NlsGge.Hierarchy.ALSampling38
import Mathlib

/-! L05b: bridge of `alV2_38` to the source formula `C:eq:V2positive` (paper/v2.tex l.2027-2039):
`V₂(u) = β₁ ∫|u|⁴ + β₂ ∫ [2|u|⁶ + 6|u|²|u'|² + ((|u|²)')²]`.
Here `u'` is the weak derivative `physicalH1DerivativeL2CLM u ∈ L²` (an a.e.-class, the project's
representation of the `H¹` derivative; it satisfies the weak-derivative test identity, see
`physicalH1DerivativeL2CLM_weakDerivativeTestIdentityAfterStarNormalizationPrerequisite`), lifted to
`ℝ` through the quotient map.  `((|u|²)')²` is stated as `(2 Re(ū u'))²`, the Leibniz form
`(|u|²)' = 2 Re(ū u')` used by the source (see `q4_integrand_eq`, "Writing ūu' = a+ib"). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace NlsGge.AblowitzLadik

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Analysis

local instance alFin38 : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure; infer_instance

/-- The weak derivative of `u ∈ H¹` as a function on `ℝ` (a representative of the `L²` class,
lifted through `ℝ → ℝ/ℤ`). -/
def alDeriv38 (u : SobolevHilbert 1) (t : ℝ) : ℂ :=
  physicalH1DerivativeL2CLM u (t : PhysicalCircle)

theorem alLiftInt38 (g : PhysicalCircle → ℝ) (hg : Integrable g spatialMeasure) :
    IntervalIntegrable (fun t : ℝ => g (t : PhysicalCircle)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hv : (volume : Measure PhysicalCircle) = spatialMeasure := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp [spatialMeasure]
  have hm := (AddCircle.measurePreserving_mk (1 : ℝ) 0)
  have := (hm.integrable_comp (g := g) (by rw [hv]; exact hg.aestronglyMeasurable)).2
    (by rw [hv]; exact hg)
  rw [zero_add] at this
  exact this

theorem alV2_eq_integral38 (β₁ β₂ : ℝ) (u : SobolevHilbert 1) :
    IntervalIntegrable (fun t : ℝ => ‖alCanon38 u t‖ ^ 4) volume 0 1 ∧
    IntervalIntegrable (fun t : ℝ => 2 * ‖alCanon38 u t‖ ^ 6
        + 6 * ‖alCanon38 u t‖ ^ 2 * ‖alDeriv38 u t‖ ^ 2
        + (2 * ((starRingEnd ℂ) (alCanon38 u t) * alDeriv38 u t).re) ^ 2) volume 0 1 ∧
    alV2_38 β₁ β₂ u =
      β₁ * (∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 4)
      + β₂ * (∫ t in (0 : ℝ)..1, (2 * ‖alCanon38 u t‖ ^ 6
        + 6 * ‖alCanon38 u t‖ ^ 2 * ‖alDeriv38 u t‖ ^ 2
        + (2 * ((starRingEnd ℂ) (alCanon38 u t) * alDeriv38 u t).re) ^ 2)) := by
  set f : C(PhysicalCircle, ℂ) := physicalH1CanonicalContinuousRepresentativeCLM u with hf
  set d : PhysicalL2 := physicalH1DerivativeL2CLM u with hd
  have hfc : ∀ t : ℝ, alCanon38 u t = f (t : PhysicalCircle) := fun t => rfl
  have hdc : ∀ t : ℝ, alDeriv38 u t = d (t : PhysicalCircle) := fun t => rfl
  simp only [hfc, hdc]
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_univ.image f.continuous).isBounded.exists_norm_le
    exact ⟨M, fun y => hM _ ⟨y, trivial, rfl⟩⟩
  have hdi : Integrable (fun y : PhysicalCircle => ‖d y‖ ^ 2) spatialMeasure := by
    have := (Lp.memLp d).integrable_norm_pow (p := 2) (by norm_num)
    simpa using this
  have hdm : AEStronglyMeasurable (fun y : PhysicalCircle => d y) spatialMeasure :=
    (Lp.memLp d).aestronglyMeasurable
  have hfm : Continuous fun y : PhysicalCircle => f y := f.continuous
  have hI1 : Integrable (fun y : PhysicalCircle => ‖f y‖ ^ 2 * ‖d y‖ ^ 2) spatialMeasure := by
    refine Integrable.mono' (hdi.const_mul (M ^ 2)) ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((hfm.norm.pow 2).aestronglyMeasurable).mul (hdm.norm.pow 2)
    · rw [Real.norm_of_nonneg (by positivity)]
      have := hM y
      have h0 : 0 ≤ ‖f y‖ := norm_nonneg _
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 this 2) (by positivity)
  have hB : Integrable (fun y : PhysicalCircle => (star (f y) * d y) ^ 2) spatialMeasure := by
    refine hI1.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((hfm.star.aestronglyMeasurable).mul hdm).pow 2
    · simp [norm_pow, norm_mul, mul_pow]
  have hE : Integrable (fun y : PhysicalCircle =>
      (2 * ((starRingEnd ℂ) (f y) * d y).re) ^ 2) spatialMeasure := by
    refine (hI1.const_mul 4).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (((Complex.continuous_re.comp_aestronglyMeasurable
        ((hfm.star.aestronglyMeasurable).mul hdm))).const_mul 2).pow 2
    · rw [Real.norm_of_nonneg (by positivity)]
      have h1 := Complex.abs_re_le_norm ((starRingEnd ℂ) (f y) * d y)
      have h2 : |((starRingEnd ℂ) (f y) * d y).re| ^ 2 ≤ ‖f y‖ ^ 2 * ‖d y‖ ^ 2 := by
        calc _ ≤ ‖(starRingEnd ℂ) (f y) * d y‖ ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) h1 2
          _ = _ := by simp [norm_mul, mul_pow]
      have : (2 * ((starRingEnd ℂ) (f y) * d y).re) ^ 2
          = 4 * |((starRingEnd ℂ) (f y) * d y).re| ^ 2 := by rw [mul_pow, sq_abs]; norm_num
      rw [this]; linarith
  have hc6 : Integrable (fun y : PhysicalCircle => ‖f y‖ ^ 6) spatialMeasure :=
    (hfm.norm.pow 6).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc4 : Integrable (fun y : PhysicalCircle => ‖f y‖ ^ 4) spatialMeasure :=
    (hfm.norm.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum : Integrable (fun y : PhysicalCircle => 2 * ‖f y‖ ^ 6 + 6 * ‖f y‖ ^ 2 * ‖d y‖ ^ 2
      + (2 * ((starRingEnd ℂ) (f y) * d y).re) ^ 2) spatialMeasure := by
    refine ((hc6.const_mul 2).add ((hI1.const_mul 6).congr (Filter.Eventually.of_forall fun y => ?_))).add hE
    simp only; ring
  refine ⟨alLiftInt38 _ hc4, alLiftInt38 _ hsum, ?_⟩
  have hQ : alV2_38 β₁ β₂ u = β₁ * ∫ y : PhysicalCircle, ‖f y‖ ^ 4 ∂spatialMeasure
      + β₂ * (2 * Complex.re (∫ y : PhysicalCircle, (star (f y) * d y) ^ 2 ∂spatialMeasure) +
        8 * (∫ y : PhysicalCircle, ‖f y‖ ^ 2 * ‖d y‖ ^ 2 ∂spatialMeasure) +
        2 * (∫ y : PhysicalCircle, ‖f y‖ ^ 6 ∂spatialMeasure)) := by
    rw [alV2_38, ← physicalH1Q4LowerOrderRemainderAfterCanonicalComponents_eq_sum_integrals,
      physicalH1QuarticIntegralAfterScalarL1Prerequisites_eq_integral]
  have hA := NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar
        (fun y : PhysicalCircle => ‖f y‖ ^ 4)
  have hS := NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar
    (fun y : PhysicalCircle => 2 * ‖f y‖ ^ 6 + 6 * ‖f y‖ ^ 2 * ‖d y‖ ^ 2
      + (2 * ((starRingEnd ℂ) (f y) * d y).re) ^ 2)
  rw [hA, hS, hQ]
  have hreB : Complex.re (∫ y : PhysicalCircle, (star (f y) * d y) ^ 2 ∂spatialMeasure)
      = ∫ y : PhysicalCircle, ((star (f y) * d y) ^ 2).re ∂spatialMeasure := by
    change Complex.reCLM _ = _
    rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM hB]
    simp
  have hRe : Integrable (fun y : PhysicalCircle => ((star (f y) * d y) ^ 2).re) spatialMeasure :=
    hB.re
  have hrhs : ∫ y : PhysicalCircle, (2 * ‖f y‖ ^ 6 + 6 * ‖f y‖ ^ 2 * ‖d y‖ ^ 2
      + (2 * ((starRingEnd ℂ) (f y) * d y).re) ^ 2) ∂spatialMeasure
      = 2 * ∫ y : PhysicalCircle, ((star (f y) * d y) ^ 2).re ∂spatialMeasure
        + 8 * ∫ y : PhysicalCircle, ‖f y‖ ^ 2 * ‖d y‖ ^ 2 ∂spatialMeasure
        + 2 * ∫ y : PhysicalCircle, ‖f y‖ ^ 6 ∂spatialMeasure := by
    have h1 : ∫ y : PhysicalCircle, (2 * ((star (f y) * d y) ^ 2).re + 8 * (‖f y‖ ^ 2 * ‖d y‖ ^ 2))
        ∂spatialMeasure = 2 * ∫ y : PhysicalCircle, ((star (f y) * d y) ^ 2).re ∂spatialMeasure
          + 8 * ∫ y : PhysicalCircle, ‖f y‖ ^ 2 * ‖d y‖ ^ 2 ∂spatialMeasure := by
      rw [integral_add (hRe.const_mul 2) (hI1.const_mul 8), integral_const_mul, integral_const_mul]
    have h2 : ∫ y : PhysicalCircle, (2 * ((star (f y) * d y) ^ 2).re + 8 * (‖f y‖ ^ 2 * ‖d y‖ ^ 2)
        + 2 * ‖f y‖ ^ 6) ∂spatialMeasure
        = (∫ y : PhysicalCircle, (2 * ((star (f y) * d y) ^ 2).re + 8 * (‖f y‖ ^ 2 * ‖d y‖ ^ 2))
        ∂spatialMeasure) + 2 * ∫ y : PhysicalCircle, ‖f y‖ ^ 6 ∂spatialMeasure := by
      rw [← integral_const_mul]
      exact integral_add ((hRe.const_mul 2).add (hI1.const_mul 8)) (hc6.const_mul 2)
    rw [h1] at h2
    rw [← h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have := NlsGge.HierarchyRiccati.Core.q4_integrand_eq (f y) (d y) 0
    simp only [norm_zero] at this
    have e2 : ((starRingEnd ℂ (f y) * d y) ^ 2).re = (f y ^ 2 * (starRingEnd ℂ) (d y) ^ 2).re := by
      have : (starRingEnd ℂ (f y) * d y) ^ 2 = (starRingEnd ℂ) (f y ^ 2 * (starRingEnd ℂ) (d y) ^ 2) := by
        simp [map_mul, map_pow, mul_pow]
      rw [this, Complex.conj_re]
    have hs : star (f y) = starRingEnd ℂ (f y) := rfl
    beta_reduce
    rw [hs, e2]
    linarith
  rw [hrhs, hreB]

end NlsGge.AblowitzLadik

#check @NlsGge.AblowitzLadik.alV2_eq_integral38
#print axioms NlsGge.AblowitzLadik.alV2_eq_integral38
