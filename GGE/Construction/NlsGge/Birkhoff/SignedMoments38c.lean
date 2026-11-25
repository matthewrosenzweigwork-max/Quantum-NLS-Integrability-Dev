import NlsGge.Birkhoff.SignedMoments38b
import NlsGge.Birkhoff.S01Equivariance38b

/-! # SIGNED-MOMENTS (`F:rem:signed`), file 3: the odd quadratic part, Parseval (`B`-free)

For a smooth period-one field `U`: `Σ_n (2πn)^{2j+1} |Û_n|²` is the imaginary part of `(-1)^j ∫ Ū ∂^{2j+1} U`
(Parseval for the `L²` inner product), hence `Im ∫₀¹ eval(formalOddQuadraticMainTerm38 j) = -Σ_n (2πn)^{2j+1}|Û_n|²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations MeasureTheory
open scoped ContDiff ComplexConjugate

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

theorem oddParseval_hasSum38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) (j : ℕ) :
    HasSum (fun n : ℤ => (-1 : ℝ) ^ j * ((2 * Real.pi * (n : ℝ)) ^ (2 * j + 1) *
        ‖smoothFourier38 U hU hper n‖ ^ 2))
      (∫ x in (0 : ℝ)..1, star (U x) * iteratedDeriv (2 * j + 1) U x).im := by
  have hdc : Continuous (iteratedDeriv (2 * j + 1) U) :=
    (fun k : ℕ => hU.continuous_iteratedDeriv k (by exact_mod_cast le_top)) (2 * j + 1)
  have hdp := NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff U hU hper (2 * j + 1)
  set F := riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper with hF
  set G := riccatiSmoothPeriodicLiftContinuousMapRecovery30First (iteratedDeriv (2 * j + 1) U) hdc hdp
    with hG
  set fL : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ F with hfL
  set gL : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ G with hgL
  have hP := (fourierBasis (T := (1 : ℝ))).hasSum_inner_mul_inner fL gL
  have hcoef : ∀ (v : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ)))) (i : ℤ),
      inner ℂ ((fourierBasis (T := (1 : ℝ))) i) v = fourierCoeff v i := fun v i =>
    (HilbertBasis.repr_apply_apply _ v i).symm.trans (fourierBasis_repr v i)
  have hgcoef : ∀ i : ℤ, fourierCoeff gL i = fourierMultiplier i ^ (2 * j + 1) * fourierCoeff fL i := by
    intro i
    have h1 := physicalFourier_liftContinuousMap_eq_fourierCoeffOnRecovery30First
      (iteratedDeriv (2 * j + 1) U) hdc hdp i
    have h2 := physicalFourier_liftContinuousMap_eq_fourierCoeffOnRecovery30First
      U hU.continuous hper i
    have h3 := riccatiFourierCoeffOn_iteratedDeriv_periodOneRecovery29 U hU hper (2 * j + 1) i
    have e1 : fourierCoeff gL i = fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (iteratedDeriv (2 * j + 1) U) i := h1
    have e2 : fourierCoeff fL i = fourierCoeffOn (by norm_num : (0 : ℝ) < 1) U i := h2
    rw [e1, e2, h3]
  have hterm : ∀ i : ℤ, (inner ℂ fL ((fourierBasis (T := (1 : ℝ))) i) *
      inner ℂ ((fourierBasis (T := (1 : ℝ))) i) gL).im =
      (-1 : ℝ) ^ j * ((2 * Real.pi * (i : ℝ)) ^ (2 * j + 1) * ‖smoothFourier38 U hU hper i‖ ^ 2) := by
    intro i
    have e1 : inner ℂ fL ((fourierBasis (T := (1 : ℝ))) i) = (starRingEnd ℂ) (fourierCoeff fL i) := by
      rw [← hcoef fL i]
      exact (inner_conj_symm _ _).symm
    have e2 : inner ℂ ((fourierBasis (T := (1 : ℝ))) i) gL =
        fourierMultiplier i ^ (2 * j + 1) * fourierCoeff fL i := by
      rw [hcoef gL i, hgcoef]
    have hs : smoothFourier38 U hU hper i = fourierCoeff fL i := rfl
    rw [e1, e2, hs]
    set c := fourierCoeff fL i
    have : (starRingEnd ℂ) c * (fourierMultiplier i ^ (2 * j + 1) * c) =
        (((-1 : ℝ) ^ j * ((2 * Real.pi * (i : ℝ)) ^ (2 * j + 1) * ‖c‖ ^ 2) : ℝ) : ℂ) * Complex.I := by
      unfold fourierMultiplier
      have h := Complex.conj_mul' c
      have hI : Complex.I ^ (2 * j + 1) = (-1 : ℂ) ^ j * Complex.I := by
        rw [pow_succ, pow_mul, Complex.I_sq]
      have hm : (2 * (Real.pi : ℂ) * Complex.I * (i : ℂ)) ^ (2 * j + 1) =
          (2 * (Real.pi : ℂ) * (i : ℂ)) ^ (2 * j + 1) * ((-1 : ℂ) ^ j * Complex.I) := by
        rw [← hI, ← mul_pow]; congr 1; ring
      rw [hm]
      push_cast
      calc (starRingEnd ℂ) c * ((2 * (Real.pi : ℂ) * (i : ℂ)) ^ (2 * j + 1) * ((-1 : ℂ) ^ j * Complex.I) * c)
          = (-1 : ℂ) ^ j * (2 * (Real.pi : ℂ) * (i : ℂ)) ^ (2 * j + 1) * Complex.I *
              ((starRingEnd ℂ) c * c) := by ring
        _ = _ := by rw [h]; ring
    rw [this, Complex.mul_I_im, Complex.ofReal_re]
  have hJ : inner ℂ fL gL = ∫ x in (0 : ℝ)..1, star (U x) * iteratedDeriv (2 * j + 1) U x := by
    rw [L2.inner_def]
    have hfae := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
      (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) F
    have hgae := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
      (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) G
    have h1 : ∫ a, inner ℂ (fL a) (gL a) ∂(AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) =
        ∫ a : PhysicalCircle, inner ℂ (F a) (G a) ∂spatialMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [hfae, hgae] with a ha hb
      rw [ha, hb]
    rw [h1, ← NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar
      (fun a : PhysicalCircle => inner ℂ (F a) (G a))]
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have ht' : t ∈ Set.Ioc (0 : ℝ) (0 + 1) := by simpa using ht
    have hFt : F (t : PhysicalCircle) = U t := AddCircle.liftIoc_coe_apply ht'
    have hGt : G (t : PhysicalCircle) = iteratedDeriv (2 * j + 1) U t :=
      AddCircle.liftIoc_coe_apply (f := iteratedDeriv (2 * j + 1) U) ht'
    simp only [hFt, hGt, RCLike.inner_apply]
    simp [mul_comm]
  have hIm := hP.mapL Complex.imCLM
  rw [hJ] at hIm
  refine hIm.congr_fun (fun n => ?_)
  rw [← hterm n]
  rfl

/-- The odd quadratic main term integrates to `-Σ_n (2πn)^{2j+1} |Û_n|²` (imaginary part). -/
theorem formalOddQuad_integral_im38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) (j : ℕ) :
    Summable (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ (2 * j + 1) * ‖smoothFourier38 U hU hper n‖ ^ 2) ∧
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation U x (formalOddQuadraticMainTerm38 j)).im =
      -∑' n : ℤ, (2 * Real.pi * (n : ℝ)) ^ (2 * j + 1) * ‖smoothFourier38 U hU hper n‖ ^ 2 := by
  have hP := oddParseval_hasSum38 U hU hper j
  have hsq : ((-1 : ℝ) ^ j) * (-1 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
  have hS : HasSum (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ (2 * j + 1) *
      ‖smoothFourier38 U hU hper n‖ ^ 2)
      ((-1 : ℝ) ^ j * (∫ x in (0 : ℝ)..1, star (U x) * iteratedDeriv (2 * j + 1) U x).im) := by
    have := hP.mul_left ((-1 : ℝ) ^ j)
    convert this using 1
    funext n
    rw [← mul_assoc, hsq, one_mul]
  refine ⟨hS.summable, ?_⟩
  rw [hS.tsum_eq]
  have hpt : ∀ x : ℝ, riccatiJetEvaluation U x (formalOddQuadraticMainTerm38 j) =
      (-1 : ℂ) ^ j * conj (star (U x) * iteratedDeriv (2 * j + 1) U x) := by
    intro x
    have h := riccatiJetFunction_eq_conjugateIf38 U (true, 2 * j + 1) x
    simp only [conjugateIf38_apply, ite_true] at h
    have h0 : riccatiJetFunction U (false, 0) x = U x := by simp [riccatiJetFunction]
    simp [formalOddQuadraticMainTerm38, riccatiJetEvaluation, polynomialEvaluation, h, h0, mul_assoc]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral_conj38]
  have hj : ((-1 : ℂ) ^ j) = (((-1 : ℝ) ^ j : ℝ) : ℂ) := by push_cast; rfl
  rw [hj, Complex.im_ofReal_mul, Complex.conj_im]
  ring

end NlsGge.Birkhoff
end
