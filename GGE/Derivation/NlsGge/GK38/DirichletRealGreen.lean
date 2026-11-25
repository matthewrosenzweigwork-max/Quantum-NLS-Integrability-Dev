import NlsGge.GK38.DirichletRealReality

/-! Actual two-parameter Green identity for the rough Dirichlet state.
Private source anchor: book I.7 Lemma 7.2 (simplicity prerequisite).
AC, AE differential identities and integrability precede integration. -/
set_option autoImplicit false
open MeasureTheory Filter
namespace NlsGge.GK38
noncomputable section
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Analysis NlsGge.Schur

/-- The independent two-parameter energy kernel. -/
def dirichletGreenKernel38 (u : PhysicalL2) (μ ν : ℂ) (s : ℝ) : ℂ :=
  actualPhysicalFloquetState33 u μ ![1, 1] s 0 * actualPhysicalFloquetState33 u ν ![1, 1] s 1 +
  actualPhysicalFloquetState33 u μ ![1, 1] s 1 * actualPhysicalFloquetState33 u ν ![1, 1] s 0

/-- Exact algebra, without real or smooth potential restrictions. -/
theorem dirichletGreen_derivative_algebra38 (U : ℝ → ℂ) (μ ν : ℂ)
    (s : ℝ) (a b : Fin 2 → ℂ) :
    ((zsCoefficientComplex U μ s).mulVec a 0 * b 1 +
      a 0 * (zsCoefficientComplex U ν s).mulVec b 1) -
    ((zsCoefficientComplex U μ s).mulVec a 1 * b 0 +
      a 1 * (zsCoefficientComplex U ν s).mulVec b 0) =
      Complex.I * (ν - μ) * (a 0 * b 1 + a 1 * b 0) := by
  simp [zsCoefficientComplex, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem dirichletGreenKernel_continuous38 (u : PhysicalL2) (μ ν : ℂ) :
    ContinuousOn (dirichletGreenKernel38 u μ ν) (Set.Icc (0 : ℝ) 2) := by
  have hc (z : ℂ) (i : Fin 2) : ContinuousOn
      (fun s => actualPhysicalFloquetState33 u z ![1, 1] s i) (Set.Icc (0 : ℝ) 2) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using
      (actualPhysicalFloquetState_AC33 u z ![1, 1] i).continuousOn
  exact ((hc μ 0).fun_mul (hc ν 1)).fun_add ((hc μ 1).fun_mul (hc ν 0))

theorem dirichletGreenKernel_integrable38 (u : PhysicalL2) (μ ν : ℂ) :
    IntervalIntegrable (dirichletGreenKernel38 u μ ν) volume 0 2 :=
  (dirichletGreenKernel_continuous38 u μ ν).intervalIntegrable_of_Icc (by norm_num)

/-- Integrated actual two-state identity on the full accepted doubled time interval. -/
theorem dirichletGreen_identity38 (u : PhysicalL2) (μ ν : ℂ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    actualPhysicalFloquetState33 u μ ![1, 1] t 0 * actualPhysicalFloquetState33 u ν ![1, 1] t 1 -
    actualPhysicalFloquetState33 u μ ![1, 1] t 1 * actualPhysicalFloquetState33 u ν ![1, 1] t 0 =
      Complex.I * (ν - μ) * ∫ s in (0 : ℝ)..t, dirichletGreenKernel38 u μ ν s := by
  have hAC : AbsolutelyContinuousOnInterval
      (fun s => actualPhysicalFloquetState33 u μ ![1, 1] s 0 * actualPhysicalFloquetState33 u ν ![1, 1] s 1 -
        actualPhysicalFloquetState33 u μ ![1, 1] s 1 * actualPhysicalFloquetState33 u ν ![1, 1] s 0) 0 2 := by
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] using!
      ((actualPhysicalFloquetState_AC33 u μ ![1, 1] 0).smul
        (actualPhysicalFloquetState_AC33 u ν ![1, 1] 1)).sub
      ((actualPhysicalFloquetState_AC33 u μ ![1, 1] 1).smul
        (actualPhysicalFloquetState_AC33 u ν ![1, 1] 0))
  have hAE : ∀ᵐ s : ℝ, s ∈ Set.uIcc (0 : ℝ) 2 →
      HasDerivAt
        (fun r => actualPhysicalFloquetState33 u μ ![1, 1] r 0 * actualPhysicalFloquetState33 u ν ![1, 1] r 1 -
          actualPhysicalFloquetState33 u μ ![1, 1] r 1 * actualPhysicalFloquetState33 u ν ![1, 1] r 0)
        (Complex.I * (ν - μ) * dirichletGreenKernel38 u μ ν s) s := by
    filter_upwards [actualPhysicalFloquetState_ae_hasDerivAt33 u μ ![1, 1] 0,
      actualPhysicalFloquetState_ae_hasDerivAt33 u μ ![1, 1] 1,
      actualPhysicalFloquetState_ae_hasDerivAt33 u ν ![1, 1] 0,
      actualPhysicalFloquetState_ae_hasDerivAt33 u ν ![1, 1] 1] with s ha0 ha1 hb0 hb1 hs
    have h := ((ha0 hs).mul (hb1 hs)).sub ((ha1 hs).mul (hb0 hs))
    have halg := dirichletGreen_derivative_algebra38
      (fun r => NlsGge.Analysis.naturalPhysicalCoverL2 u (r : SpectralCircle)) μ ν s
      (actualPhysicalFloquetState33 u μ ![1, 1] s) (actualPhysicalFloquetState33 u ν ![1, 1] s)
    rw [halg] at h
    exact h
  have hInt := (dirichletGreenKernel_integrable38 u μ ν).const_mul (Complex.I * (ν - μ))
  have hp := complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt hAC hInt hAE
  have htu : t ∈ Set.uIcc (0 : ℝ) 2 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have h := hp t htu
  simpa only [actualPhysicalFloquetState_initial33, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, sub_self, zero_add, intervalIntegral.integral_const_mul] using h

end
end NlsGge.GK38
