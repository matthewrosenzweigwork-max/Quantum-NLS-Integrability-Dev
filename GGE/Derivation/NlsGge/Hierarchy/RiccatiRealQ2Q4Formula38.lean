import NlsGge.Hierarchy.RiccatiRealQ6Formula38

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! Real local formulas for `Q₀`, `Q₂`, `Q₄` (paper/v2.tex, eq. `eq:firstcharges` and the
`Q₄` formulas `C:eq:Q4`, specialized to real fields where `2 Re(u² \bar{u'}²) = 2u²u'²`).

Route as for `Q₆`: evaluate the formal density `formalChargeIntegrand j` on a real field,
and subtract the final density; the difference is the derivative of an explicit periodic
flux. -/

noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open scoped ContDiff Interval
open MeasureTheory

private theorem iteratedDeriv_contDiffC24 (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv n hf

private theorem hasDerivAt_iteratedDeriv24 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (k : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv k U) (iteratedDeriv (k + 1) U x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv k U) x :=
    ((iteratedDeriv_contDiffC24 U hU k).differentiable (by simp)).differentiableAt
  have h := hd.hasDerivAt
  rwa [← iteratedDeriv_succ] at h

private theorem jetFunction_real24 (u : ℝ → ℝ) (x : ℝ) (v : Jet) :
    riccatiJetFunction (fun y => (u y : ℂ)) v x =
      iteratedDeriv v.2 (fun y => (u y : ℂ)) x := by
  have hstar : (fun y => star ((u y : ℝ) : ℂ)) = fun y => (u y : ℂ) := by
    funext y
    simp
  rcases v with ⟨b, n⟩
  cases b
  · simp [riccatiJetFunction]
  · simp [riccatiJetFunction, hstar]

/-- Evaluation of the formal `Q₀` density on a real field. -/
theorem realQ0_evaluation38 (u : ℝ → ℝ) (x : ℝ) :
    riccatiJetEvaluation (fun y => (u y : ℂ)) x (formalChargeIntegrand 0) =
      (iteratedDeriv 0 (fun y => (u y : ℂ)) x) ^ 2 := by
  have hv := jetFunction_real24 u x
  unfold riccatiJetEvaluation formalChargeIntegrand
  rw [show 2 * 0 + 1 = 1 from rfl, p_one]
  simp only [map_mul, map_add, map_sub, map_neg, map_pow, polynomialEvaluation_X,
    polynomialEvaluation_C, hv, map_ofNat]
  push_cast
  norm_num
  ring

/-- Evaluation of the formal `Q₂` density on a real field. -/
theorem realQ2_evaluation38 (u : ℝ → ℝ) (x : ℝ) :
    riccatiJetEvaluation (fun y => (u y : ℂ)) x (formalChargeIntegrand 1) =
      (iteratedDeriv 0 (fun y => (u y : ℂ)) x) ^ 4
      - iteratedDeriv 0 (fun y => (u y : ℂ)) x * iteratedDeriv 2 (fun y => (u y : ℂ)) x := by
  have hv := jetFunction_real24 u x
  unfold riccatiJetEvaluation formalChargeIntegrand
  rw [show 2 * 1 + 1 = 3 from rfl, p_three]
  simp only [map_mul, map_add, map_sub, map_neg, map_pow, polynomialEvaluation_X,
    polynomialEvaluation_C, hv, map_ofNat]
  push_cast
  norm_num
  ring

/-- Evaluation of the formal `Q₄` density on a real field. -/
theorem realQ4_evaluation38 (u : ℝ → ℝ) (x : ℝ) :
    riccatiJetEvaluation (fun y => (u y : ℂ)) x (formalChargeIntegrand 2) =
      2 * (iteratedDeriv 0 (fun y => (u y : ℂ)) x) ^ 6
      - 7 * (iteratedDeriv 0 (fun y => (u y : ℂ)) x) ^ 3
          * iteratedDeriv 2 (fun y => (u y : ℂ)) x
      - 11 * (iteratedDeriv 0 (fun y => (u y : ℂ)) x) ^ 2
          * (iteratedDeriv 1 (fun y => (u y : ℂ)) x) ^ 2
      + iteratedDeriv 0 (fun y => (u y : ℂ)) x * iteratedDeriv 4 (fun y => (u y : ℂ)) x := by
  have hv := jetFunction_real24 u x
  unfold riccatiJetEvaluation formalChargeIntegrand
  rw [show 2 * 2 + 1 = 5 from rfl, p_five_after_natCast_prerequisite]
  simp only [map_mul, map_add, map_sub, map_neg, map_pow, polynomialEvaluation_X,
    polynomialEvaluation_C, hv, map_ofNat]
  push_cast
  norm_num
  ring

/-! ### Fluxes -/

private def flux2_24 (U : ℝ → ℂ) (x : ℝ) : ℂ :=
  - (iteratedDeriv 0 U x * iteratedDeriv 1 U x)

private def flux4_24 (U : ℝ → ℂ) (x : ℝ) : ℂ :=
  iteratedDeriv 0 U x * iteratedDeriv 3 U x - iteratedDeriv 1 U x * iteratedDeriv 2 U x
    - 7 * iteratedDeriv 0 U x ^ 3 * iteratedDeriv 1 U x

private theorem flux2_24_hasDerivAt (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (x : ℝ) :
    HasDerivAt (flux2_24 U)
      (((iteratedDeriv 0 U x) ^ 4 - iteratedDeriv 0 U x * iteratedDeriv 2 U x)
        - ((iteratedDeriv 1 U x) ^ 2 + (iteratedDeriv 0 U x) ^ 4)) x := by
  have h0 := hasDerivAt_iteratedDeriv24 U hU 0 x
  have h1 := hasDerivAt_iteratedDeriv24 U hU 1 x
  have h := (h0.mul h1).neg
  refine HasDerivAt.congr_deriv (h.congr_of_eventuallyEq ?_) ?_
  · refine Filter.Eventually.of_forall fun y => ?_
    simp only [flux2_24, Pi.mul_apply, Pi.neg_apply]
  · simp only [Nat.reduceAdd, Nat.cast_ofNat]
    ring

private theorem flux4_24_hasDerivAt (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (x : ℝ) :
    HasDerivAt (flux4_24 U)
      ((2 * (iteratedDeriv 0 U x) ^ 6
        - 7 * (iteratedDeriv 0 U x) ^ 3 * iteratedDeriv 2 U x
        - 11 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 1 U x) ^ 2
        + iteratedDeriv 0 U x * iteratedDeriv 4 U x)
       - ((iteratedDeriv 2 U x) ^ 2 + 10 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 1 U x) ^ 2
          + 2 * (iteratedDeriv 0 U x) ^ 6)) x := by
  have h0 := hasDerivAt_iteratedDeriv24 U hU 0 x
  have h1 := hasDerivAt_iteratedDeriv24 U hU 1 x
  have h2 := hasDerivAt_iteratedDeriv24 U hU 2 x
  have h3 := hasDerivAt_iteratedDeriv24 U hU 3 x
  have h := (((h0.mul h3).sub (h1.mul h2)).sub (((h0.pow 3).const_mul 7).mul h1))
  refine HasDerivAt.congr_deriv (h.congr_of_eventuallyEq ?_) ?_
  · refine Filter.Eventually.of_forall fun y => ?_
    simp only [flux4_24, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Pi.pow_apply]
    ring

private theorem flux2_24_periodic (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) : Function.Periodic (flux2_24 U) 1 := by
  intro x
  have hp := fun k : ℕ => NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff U hU hper k x
  simp only [flux2_24, hp]

private theorem flux4_24_periodic (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) : Function.Periodic (flux4_24 U) 1 := by
  intro x
  have hp := fun k : ℕ => NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff U hU hper k x
  simp only [flux4_24, hp]

/-- The explicit real `Q₀` local formula. -/
theorem realQ0_local_formula38 (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation (fun y => (u y : ℂ)) x (formalChargeIntegrand 0)) =
      ((∫ x in (0 : ℝ)..1, (u x) ^ 2 : ℝ) : ℂ) := by
  have _ := hper
  have _ := hu
  have hlhs : (fun x => riccatiJetEvaluation (fun y => (u y : ℂ)) x (formalChargeIntegrand 0)) =
      fun x => (((u x) ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [realQ0_evaluation38]
    simp
  rw [hlhs]
  exact intervalIntegral.integral_ofReal

/-- The explicit real `Q₂` local formula. -/
theorem realQ2_local_formula38 (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation (fun y => (u y : ℂ)) x (formalChargeIntegrand 1)) =
      ((∫ x in (0 : ℝ)..1, ((deriv u x) ^ 2 + (u x) ^ 4) : ℝ) : ℂ) := by
  set U : ℝ → ℂ := fun y => (u y : ℂ) with hUdef
  have hU : ContDiff ℝ ∞ U := Complex.ofRealCLM.contDiff.comp hu
  have hUper : Function.Periodic U 1 := by
    intro x
    simp only [hUdef, hper x]
  have hcontk : ∀ k : ℕ, Continuous (iteratedDeriv k U) := fun k =>
    (iteratedDeriv_contDiffC24 U hU k).continuous
  have hpre : Continuous (fun x => (iteratedDeriv 0 U x) ^ 4
      - iteratedDeriv 0 U x * iteratedDeriv 2 U x) := by
    have := hcontk 0; have := hcontk 2
    fun_prop
  have hfin : Continuous (fun x => (iteratedDeriv 1 U x) ^ 2 + (iteratedDeriv 0 U x) ^ 4) := by
    have := hcontk 0; have := hcontk 1
    fun_prop
  have hint : IntervalIntegrable (fun x => ((iteratedDeriv 0 U x) ^ 4
      - iteratedDeriv 0 U x * iteratedDeriv 2 U x)
      - ((iteratedDeriv 1 U x) ^ 2 + (iteratedDeriv 0 U x) ^ 4))
      MeasureTheory.volume 0 1 := (hpre.sub hfin).intervalIntegrable 0 1
  have hzero : (∫ x in (0 : ℝ)..1, (((iteratedDeriv 0 U x) ^ 4
      - iteratedDeriv 0 U x * iteratedDeriv 2 U x)
      - ((iteratedDeriv 1 U x) ^ 2 + (iteratedDeriv 0 U x) ^ 4))) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => flux2_24_hasDerivAt U hU x) hint]
    have := flux2_24_periodic U hU hUper 0
    rw [zero_add] at this
    rw [this, sub_self]
  have hsplit : (∫ x in (0 : ℝ)..1, ((iteratedDeriv 0 U x) ^ 4
      - iteratedDeriv 0 U x * iteratedDeriv 2 U x)) =
      ∫ x in (0 : ℝ)..1, ((iteratedDeriv 1 U x) ^ 2 + (iteratedDeriv 0 U x) ^ 4) := by
    rw [intervalIntegral.integral_sub (hpre.intervalIntegrable 0 1)
      (hfin.intervalIntegrable 0 1)] at hzero
    exact sub_eq_zero.mp hzero
  have hlhs : (fun x => riccatiJetEvaluation U x (formalChargeIntegrand 1)) =
      fun x => (iteratedDeriv 0 U x) ^ 4 - iteratedDeriv 0 U x * iteratedDeriv 2 U x := by
    funext x
    exact realQ2_evaluation38 u x
  have hrhs : (fun x => (iteratedDeriv 1 U x) ^ 2 + (iteratedDeriv 0 U x) ^ 4) = fun x =>
      ((((deriv u x) ^ 2 + (u x) ^ 4 : ℝ)) : ℂ) := by
    funext x
    have e := fun k : ℕ => congrFun (iteratedDeriv_ofReal38 u hu k) x
    simp only [hUdef, e]
    rw [← iteratedDeriv_one]
    push_cast
    simp only [iteratedDeriv_zero]
  rw [hlhs, hsplit, hrhs]
  exact intervalIntegral.integral_ofReal

/-- The explicit real `Q₄` local formula. -/
theorem realQ4_local_formula38 (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation (fun y => (u y : ℂ)) x (formalChargeIntegrand 2)) =
      ((∫ x in (0 : ℝ)..1,
        ((iteratedDeriv 2 u x) ^ 2 + 10 * (u x) ^ 2 * (deriv u x) ^ 2 + 2 * (u x) ^ 6) : ℝ)
        : ℂ) := by
  set U : ℝ → ℂ := fun y => (u y : ℂ) with hUdef
  have hU : ContDiff ℝ ∞ U := Complex.ofRealCLM.contDiff.comp hu
  have hUper : Function.Periodic U 1 := by
    intro x
    simp only [hUdef, hper x]
  have hcontk : ∀ k : ℕ, Continuous (iteratedDeriv k U) := fun k =>
    (iteratedDeriv_contDiffC24 U hU k).continuous
  have hpre : Continuous (fun x => 2 * (iteratedDeriv 0 U x) ^ 6
        - 7 * (iteratedDeriv 0 U x) ^ 3 * iteratedDeriv 2 U x
        - 11 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 1 U x) ^ 2
        + iteratedDeriv 0 U x * iteratedDeriv 4 U x) := by
    have := hcontk 0; have := hcontk 1; have := hcontk 2; have := hcontk 4
    fun_prop
  have hfin : Continuous (fun x => (iteratedDeriv 2 U x) ^ 2
      + 10 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 1 U x) ^ 2
      + 2 * (iteratedDeriv 0 U x) ^ 6) := by
    have := hcontk 0; have := hcontk 1; have := hcontk 2
    fun_prop
  have hint : IntervalIntegrable (fun x => (2 * (iteratedDeriv 0 U x) ^ 6
        - 7 * (iteratedDeriv 0 U x) ^ 3 * iteratedDeriv 2 U x
        - 11 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 1 U x) ^ 2
        + iteratedDeriv 0 U x * iteratedDeriv 4 U x)
       - ((iteratedDeriv 2 U x) ^ 2 + 10 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 1 U x) ^ 2
          + 2 * (iteratedDeriv 0 U x) ^ 6)) MeasureTheory.volume 0 1 :=
    (hpre.sub hfin).intervalIntegrable 0 1
  have hzero : (∫ x in (0 : ℝ)..1, ((2 * (iteratedDeriv 0 U x) ^ 6
        - 7 * (iteratedDeriv 0 U x) ^ 3 * iteratedDeriv 2 U x
        - 11 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 1 U x) ^ 2
        + iteratedDeriv 0 U x * iteratedDeriv 4 U x)
       - ((iteratedDeriv 2 U x) ^ 2 + 10 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 1 U x) ^ 2
          + 2 * (iteratedDeriv 0 U x) ^ 6))) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => flux4_24_hasDerivAt U hU x) hint]
    have := flux4_24_periodic U hU hUper 0
    rw [zero_add] at this
    rw [this, sub_self]
  have hsplit : (∫ x in (0 : ℝ)..1, (2 * (iteratedDeriv 0 U x) ^ 6
        - 7 * (iteratedDeriv 0 U x) ^ 3 * iteratedDeriv 2 U x
        - 11 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 1 U x) ^ 2
        + iteratedDeriv 0 U x * iteratedDeriv 4 U x)) =
      ∫ x in (0 : ℝ)..1, ((iteratedDeriv 2 U x) ^ 2
        + 10 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 1 U x) ^ 2
        + 2 * (iteratedDeriv 0 U x) ^ 6) := by
    rw [intervalIntegral.integral_sub (hpre.intervalIntegrable 0 1)
      (hfin.intervalIntegrable 0 1)] at hzero
    exact sub_eq_zero.mp hzero
  have hlhs : (fun x => riccatiJetEvaluation U x (formalChargeIntegrand 2)) =
      fun x => 2 * (iteratedDeriv 0 U x) ^ 6
        - 7 * (iteratedDeriv 0 U x) ^ 3 * iteratedDeriv 2 U x
        - 11 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 1 U x) ^ 2
        + iteratedDeriv 0 U x * iteratedDeriv 4 U x := by
    funext x
    exact realQ4_evaluation38 u x
  have hrhs : (fun x => (iteratedDeriv 2 U x) ^ 2
      + 10 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 1 U x) ^ 2
      + 2 * (iteratedDeriv 0 U x) ^ 6) = fun x =>
      ((((iteratedDeriv 2 u x) ^ 2 + 10 * (u x) ^ 2 * (deriv u x) ^ 2 + 2 * (u x) ^ 6 : ℝ)) : ℂ) := by
    funext x
    have e := fun k : ℕ => congrFun (iteratedDeriv_ofReal38 u hu k) x
    simp only [hUdef, e]
    rw [← iteratedDeriv_one]
    push_cast
    simp only [iteratedDeriv_zero]
  rw [hlhs, hsplit, hrhs]
  exact intervalIntegral.integral_ofReal


end NlsGge.HierarchyRiccati.Core

end
