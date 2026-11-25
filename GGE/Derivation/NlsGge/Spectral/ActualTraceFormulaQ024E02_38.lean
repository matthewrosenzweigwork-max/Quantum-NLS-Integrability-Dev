import NlsGge.Spectral.ActualTraceFormulaE02_38
import NlsGge.Hierarchy.RiccatiRealQ2Q4Formula38
import NlsGge.Hierarchy.RiccatiQ4SmoothDensityPointwiseAfterCheckedAlgebraAndStarPrerequisites
import NlsGge.Hierarchy.RiccatiQ2PeriodicIntegration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff ComplexConjugate
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
open NlsGge.HierarchyRiccati NlsGge.HierarchyRiccati.Core

/-! # E02.06 explicit checks: the trace formula for `Q₀`, `Q₂`, `Q₄` with `v = actualGapHeightE02_38 u`.

Normalizations (paper/v2.tex lines 61-77): `Q₀ = ∫|u|²`, `Q₂ = ∫(|u'|²+|u|⁴)`,
`Q₄ = ∫(|u''|² + 2|u|⁶ + 8|u|²|u'|² + 2 Re(u² conj(u')²))`. -/

private theorem jetFn_complex_Q024 (U : ℝ → ℂ) (x : ℝ) (b : Bool) (n : ℕ) :
    riccatiJetFunction U (b, n) x =
      if b then star (iteratedDeriv n U x) else iteratedDeriv n U x := by
  cases b
  · simp [riccatiJetFunction]
  · simp only [riccatiJetFunction, if_true]
    exact congrFun (iteratedDeriv_star_prerequisite U n) x

private theorem Q0_eval_Q024 (U : ℝ → ℂ) (x : ℝ) :
    riccatiJetEvaluation U x (formalChargeIntegrand 0) = star (U x) * U x := by
  have hv := jetFn_complex_Q024 U x
  unfold riccatiJetEvaluation formalChargeIntegrand
  rw [show 2 * 0 + 1 = 1 from rfl, p_one]
  simp only [map_mul, map_add, map_sub, map_neg, map_pow, polynomialEvaluation_X,
    polynomialEvaluation_C, hv, map_ofNat]
  simp
  ring

private theorem Q2_eval_Q024 (U : ℝ → ℂ) (x : ℝ) :
    riccatiJetEvaluation U x (formalChargeIntegrand 1) =
      -(U x * star (iteratedDeriv 2 U x)) + (star (U x) * U x) ^ 2 := by
  have hv := jetFn_complex_Q024 U x
  unfold riccatiJetEvaluation formalChargeIntegrand
  rw [show 2 * 1 + 1 = 3 from rfl, p_three]
  simp only [map_mul, map_add, map_sub, map_neg, map_pow, polynomialEvaluation_X,
    polynomialEvaluation_C, hv, map_ofNat]
  simp
  ring

private theorem iterContDiff_Q024 (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv n hf

/-- Complex Q₀ local formula: `∫₀¹ formal charge 0 = ∫₀¹ |U|²`. -/
theorem complexQ0_local_formula_Q024 (U : ℝ → ℂ) :
    (∫ x in (0:ℝ)..1, riccatiJetEvaluation U x (formalChargeIntegrand 0)).re =
      ∫ x in (0:ℝ)..1, ‖U x‖ ^ 2 := by
  have h : (fun x => riccatiJetEvaluation U x (formalChargeIntegrand 0)) =
      fun x => (((‖U x‖ ^ 2 : ℝ)) : ℂ) := by
    funext x
    rw [Q0_eval_Q024, Complex.star_def, Complex.conj_mul']
    push_cast; rfl
  rw [h, intervalIntegral.integral_ofReal, Complex.ofReal_re]

/-- Complex Q₂ local formula. -/
theorem complexQ2_local_formula_Q024 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) :
    (∫ x in (0:ℝ)..1, riccatiJetEvaluation U x (formalChargeIntegrand 1)).re =
      ∫ x in (0:ℝ)..1, (‖deriv U x‖ ^ 2 + ‖U x‖ ^ 4) := by
  have hd : ∀ k : ℕ, ContDiff ℝ ∞ (iteratedDeriv k U) := iterContDiff_Q024 U hU
  have hstarU : ContDiff ℝ ∞ (fun x => star (U x)) :=
    ((starL ℝ : ℂ ≃L⋆[ℝ] ℂ).toContinuousLinearMap).contDiff.comp hU
  have hpk : ∀ k : ℕ, Function.Periodic (iteratedDeriv k U) 1 :=
    fun k => periodic_iteratedDeriv_of_contDiff U hU hper k
  have hder : ∀ k : ℕ, ∀ x, HasDerivAt (iteratedDeriv k U) (iteratedDeriv (k+1) U x) x := by
    intro k x
    have h := (((hd k).differentiable (by simp)).differentiableAt (x := x)).hasDerivAt
    rwa [← iteratedDeriv_succ] at h
  set flux : ℝ → ℂ := fun x => -(U x * star (iteratedDeriv 1 U x)) with hflux
  have hstarder : ∀ x, HasDerivAt (fun y => star (iteratedDeriv 1 U y))
      (star (iteratedDeriv 2 U x)) x := by
    intro x
    exact (hder 1 x).star
  have hfd : ∀ x, HasDerivAt flux
      (-(iteratedDeriv 1 U x * star (iteratedDeriv 1 U x) + U x * star (iteratedDeriv 2 U x))) x := by
    intro x
    have h0 : HasDerivAt U (iteratedDeriv 1 U x) x := by
      simpa using hder 0 x
    exact (h0.mul (hstarder x)).neg
  have hcontJ : Continuous (fun x => riccatiJetEvaluation U x (formalChargeIntegrand 1)) := by
    simp only [Q2_eval_Q024]
    have h2 : Continuous (fun x => star (iteratedDeriv 2 U x)) :=
      continuous_star.comp (hd 2).continuous
    have h0 := hU.continuous
    have h0s : Continuous (fun x => star (U x)) := continuous_star.comp h0
    fun_prop
  have hcontE : Continuous (fun x => iteratedDeriv 1 U x * star (iteratedDeriv 1 U x)
      + (star (U x) * U x) ^ 2) := by
    have h1 := (hd 1).continuous
    have h1s : Continuous (fun x => star (iteratedDeriv 1 U x)) := continuous_star.comp h1
    have h0 := hU.continuous
    have h0s : Continuous (fun x => star (U x)) := continuous_star.comp h0
    fun_prop
  have hdiffeq : ∀ x, riccatiJetEvaluation U x (formalChargeIntegrand 1)
      - (iteratedDeriv 1 U x * star (iteratedDeriv 1 U x) + (star (U x) * U x) ^ 2)
      = -(iteratedDeriv 1 U x * star (iteratedDeriv 1 U x) + U x * star (iteratedDeriv 2 U x)) := by
    intro x; rw [Q2_eval_Q024]; ring
  have hzero : (∫ x in (0:ℝ)..1, (riccatiJetEvaluation U x (formalChargeIntegrand 1)
      - (iteratedDeriv 1 U x * star (iteratedDeriv 1 U x) + (star (U x) * U x) ^ 2))) = 0 := by
    simp only [hdiffeq]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hfd x)
      (by
        have hc : Continuous (fun x => -(iteratedDeriv 1 U x * star (iteratedDeriv 1 U x)
            + U x * star (iteratedDeriv 2 U x))) := by
          have := hcontJ.sub hcontE
          convert this using 1
          funext x
          exact (hdiffeq x).symm
        exact hc.intervalIntegrable 0 1)]
    have : flux 1 = flux 0 := by
      have := hpk 0 0
      have h1 := hpk 1 0
      simp only [hflux, zero_add] at this h1 ⊢
      simp only [iteratedDeriv_zero] at this
      rw [this, h1]
    rw [this, sub_self]
  rw [intervalIntegral.integral_sub (hcontJ.intervalIntegrable 0 1) (hcontE.intervalIntegrable 0 1),
    sub_eq_zero] at hzero
  rw [hzero]
  have : (fun x => iteratedDeriv 1 U x * star (iteratedDeriv 1 U x) + (star (U x) * U x) ^ 2) =
      fun x => (((‖deriv U x‖ ^ 2 + ‖U x‖ ^ 4 : ℝ)) : ℂ) := by
    funext x
    rw [iteratedDeriv_one, Complex.star_def, Complex.mul_conj', Complex.conj_mul']
    push_cast
    ring
  rw [this, intervalIntegral.integral_ofReal, Complex.ofReal_re]

/-- Complex Q₄ local formula (v2 `C:eq:Q4`, first form). -/
theorem complexQ4_local_formula_Q024 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) :
    (∫ x in (0:ℝ)..1, riccatiJetEvaluation U x (formalChargeIntegrand 2)).re =
      ∫ x in (0:ℝ)..1, (‖iteratedDeriv 2 U x‖ ^ 2 + 2 * ‖U x‖ ^ 6
        + 8 * ‖U x‖ ^ 2 * ‖deriv U x‖ ^ 2
        + 2 * (U x ^ 2 * (star (deriv U x)) ^ 2).re) := by
  have h := q4_smooth_periodic_source_integral_identity_after_evaluation_prerequisites U hU hper
  have hs : (fun x => riccatiJetEvaluation U x (formalChargeIntegrand 2)) =
      q4SourceDensityAfterEvaluationPrerequisites U := rfl
  rw [hs, h]
  have hcontE : Continuous (q4EnergyDensityAfterEvaluationPrerequisites U) := by
    unfold q4EnergyDensityAfterEvaluationPrerequisites
    have h0 := hU.continuous
    have hk : ∀ k : ℕ, Continuous (iteratedDeriv k U) := fun k => (iterContDiff_Q024 U hU k).continuous
    have hks : ∀ k : ℕ, Continuous (iteratedDeriv k (fun y => star (U y))) := by
      intro k
      rw [iteratedDeriv_star_prerequisite U k]
      exact continuous_star.comp (hk k)
    have h0s : Continuous (fun x => star (U x)) := continuous_star.comp h0
    have := hk 1; have := hk 2; have := hks 1; have := hks 2
    fun_prop
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  show RCLike.re (K := ℂ) _ = _
  rw [← integral_re (hcontE.integrableOn_Ioc)]
  congr 1
  funext x
  show (q4EnergyDensityAfterEvaluationPrerequisites U x).re = _
  rw [q4EnergyDensity_eq_h2_leading_add_lower_order_after_checked_prerequisites]
  unfold q4SmoothLowerOrderRealDensityAfterCheckedPrerequisites
  have hc : (U x ^ 2 * (star (deriv U x)) ^ 2).re = ((star (U x) * iteratedDeriv 1 U x) ^ 2).re := by
    have : U x ^ 2 * (star (deriv U x)) ^ 2 = star ((star (U x) * iteratedDeriv 1 U x) ^ 2) := by
      rw [iteratedDeriv_one]; simp [mul_pow]
    rw [this]; exact Complex.conj_re _
  rw [hc, iteratedDeriv_one]
  ring

/-- E02.06 (a), `Q₀`, complex field. -/
theorem actualTraceFormula_Q0_complex_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (U : ℝ → ℂ) (hUs : ContDiff ℝ ∞ U) (hUp : Function.Periodic U 1)
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 2)] U) :
    (2/Real.pi) * ∫ t : ℝ, actualGapHeightE02_38 u t = ∫ x in (0:ℝ)..1, ‖U x‖ ^ 2 := by
  have h := (actualTraceFormula_E02_38 u hu U hUs hUp hae 0).2
  rw [complexQ0_local_formula_Q024 U] at h
  simpa using h.symm

/-- E02.06 (a), `Q₂`, complex field. -/
theorem actualTraceFormula_Q2_complex_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (U : ℝ → ℂ) (hUs : ContDiff ℝ ∞ U) (hUp : Function.Periodic U 1)
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 2)] U) :
    (2/Real.pi) * ∫ t : ℝ, (2*t)^2 * actualGapHeightE02_38 u t =
      ∫ x in (0:ℝ)..1, (‖deriv U x‖ ^ 2 + ‖U x‖ ^ 4) := by
  have h := (actualTraceFormula_E02_38 u hu U hUs hUp hae 1).2
  rw [complexQ2_local_formula_Q024 U hUs hUp] at h
  simpa using h.symm

/-- E02.06 (a), `Q₄`, complex field (v2 `C:eq:Q4`, first form). -/
theorem actualTraceFormula_Q4_complex_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (U : ℝ → ℂ) (hUs : ContDiff ℝ ∞ U) (hUp : Function.Periodic U 1)
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 2)] U) :
    (2/Real.pi) * ∫ t : ℝ, (2*t)^4 * actualGapHeightE02_38 u t =
      ∫ x in (0:ℝ)..1, (‖iteratedDeriv 2 U x‖ ^ 2 + 2 * ‖U x‖ ^ 6
        + 8 * ‖U x‖ ^ 2 * ‖deriv U x‖ ^ 2
        + 2 * (U x ^ 2 * (star (deriv U x)) ^ 2).re) := by
  have h := (actualTraceFormula_E02_38 u hu U hUs hUp hae 2).2
  rw [complexQ4_local_formula_Q024 U hUs hUp] at h
  simpa using h.symm

private theorem real_cast_Q024 (w : ℝ → ℝ) (hws : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun y => (w y : ℂ)) := Complex.ofRealCLM.contDiff.comp hws

private theorem real_cast_per_Q024 (w : ℝ → ℝ) (hwp : Function.Periodic w 1) :
    Function.Periodic (fun y => (w y : ℂ)) 1 := by
  intro x; simp only [hwp x]

/-- E02.06 (b), `Q₀`, real field. -/
theorem actualTraceFormula_Q0_real_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (w : ℝ → ℝ) (hws : ContDiff ℝ ∞ w) (hwp : Function.Periodic w 1)
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 2)] (fun y => (w y : ℂ))) :
    (2/Real.pi) * ∫ t : ℝ, actualGapHeightE02_38 u t = ∫ x in (0:ℝ)..1, (w x) ^ 2 := by
  have h := (actualTraceFormula_E02_38 u hu (fun y => (w y : ℂ)) (real_cast_Q024 w hws)
    (real_cast_per_Q024 w hwp) hae 0).2
  rw [realQ0_local_formula38 w hws hwp, Complex.ofReal_re] at h
  simpa using h.symm

/-- E02.06 (b), `Q₂`, real field. -/
theorem actualTraceFormula_Q2_real_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (w : ℝ → ℝ) (hws : ContDiff ℝ ∞ w) (hwp : Function.Periodic w 1)
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 2)] (fun y => (w y : ℂ))) :
    (2/Real.pi) * ∫ t : ℝ, (2*t)^2 * actualGapHeightE02_38 u t =
      ∫ x in (0:ℝ)..1, ((deriv w x) ^ 2 + (w x) ^ 4) := by
  have h := (actualTraceFormula_E02_38 u hu (fun y => (w y : ℂ)) (real_cast_Q024 w hws)
    (real_cast_per_Q024 w hwp) hae 1).2
  rw [realQ2_local_formula38 w hws hwp, Complex.ofReal_re] at h
  simpa using h.symm

/-- E02.06 (b), `Q₄`, real field (`2Re(w²w'²) = 2w²w'²`, so `8+2 = 10`). -/
theorem actualTraceFormula_Q4_real_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (w : ℝ → ℝ) (hws : ContDiff ℝ ∞ w) (hwp : Function.Periodic w 1)
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 2)] (fun y => (w y : ℂ))) :
    (2/Real.pi) * ∫ t : ℝ, (2*t)^4 * actualGapHeightE02_38 u t =
      ∫ x in (0:ℝ)..1,
        ((iteratedDeriv 2 w x) ^ 2 + 10 * (w x) ^ 2 * (deriv w x) ^ 2 + 2 * (w x) ^ 6) := by
  have h := (actualTraceFormula_E02_38 u hu (fun y => (w y : ℂ)) (real_cast_Q024 w hws)
    (real_cast_per_Q024 w hwp) hae 2).2
  rw [realQ4_local_formula38 w hws hwp, Complex.ofReal_re] at h
  simpa using h.symm

end NlsGge.SpectralFoundations
end
