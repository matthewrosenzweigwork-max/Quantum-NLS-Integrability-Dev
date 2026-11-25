import NlsGge.Hierarchy.RiccatiLowOrderAlgebraAfterCore
import NlsGge.Hierarchy.RiccatiSmoothJetDerivativeAfterProductPrerequisite
import NlsGge.Hierarchy.RiccatiDerivativeExcessAndPeriodicEvaluatorRecoverySecond
import NlsGge.Hierarchy.RiccatiQ4IteratedDerivStarPrerequisiteThird
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! Batch 38: analytic prerequisites for the reality of the local charges.

* evaluation of the jet swap `u ↔ ū` is complex conjugation;
* the period integral of a formal total derivative vanishes;
* conditional reality: if `k! (u p_k - ū σ(p_k))` is a formal total
  derivative, then `∫₀¹ u p_k` is real.

The algebraic hypothesis is discharged separately (formal Wronskian identity);
that is an E06-only argument, different from the source's spectral route. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory
open scoped ContDiff ComplexConjugate

/-- The jet swap `(b,k) ↦ (!b,k)`, i.e. formal conjugation `u ↔ ū`. -/
def jetSwapHom38 : Poly →+* Poly :=
  (MvPolynomial.rename (fun v : Jet => (!v.1, v.2))).toRingHom

@[simp] theorem jetSwapHom38_X (v : Jet) :
    jetSwapHom38 (MvPolynomial.X v) = MvPolynomial.X (!v.1, v.2) := by
  simp [jetSwapHom38]

theorem riccatiJetFunction_swap38 (u : ℝ → ℂ) (v : Jet) (x : ℝ) :
    riccatiJetFunction u (!v.1, v.2) x = conj (riccatiJetFunction u v x) := by
  rcases v with ⟨b, k⟩
  have h := congrFun (iteratedDeriv_star_prerequisite u k) x
  cases b
  · simpa [riccatiJetFunction] using h
  · simp only [riccatiJetFunction, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [h]
    simp

/-- Evaluating the swapped polynomial is complex conjugation. -/
theorem riccatiJetEvaluation_swap38 (u : ℝ → ℂ) (x : ℝ) (P : Poly) :
    riccatiJetEvaluation u x (jetSwapHom38 P) = conj (riccatiJetEvaluation u x P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp [jetSwapHom38, riccatiJetEvaluation, polynomialEvaluation]
  | add P Q hP hQ =>
      simp only [map_add, riccatiJetEvaluation] at hP hQ ⊢
      rw [hP, hQ]
  | mul_X P v hP =>
      simp only [map_mul, riccatiJetEvaluation] at hP ⊢
      rw [hP, jetSwapHom38_X]
      simp only [polynomialEvaluation_X]
      rw [riccatiJetFunction_swap38]

/-- The period integral of a formal total derivative vanishes. -/
theorem riccatiJetEvaluation_integral_spatialD38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (ℓ : Poly) :
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (spatialD ℓ)) = 0 := by
  have hcont : Continuous (fun x => riccatiJetEvaluation u x (spatialD ℓ)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (riccatiJetEvaluation_hasDerivAt u hu (spatialD ℓ) x).continuousAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => riccatiJetEvaluation_hasDerivAt u hu ℓ x)
    (hcont.intervalIntegrable _ _)]
  have h := riccatiJetEvaluation_periodic_of_smooth_periodicNativeRecovery u hu hper ℓ 0
  simp only [zero_add] at h
  rw [h, sub_self]

theorem intervalIntegral_conj38 (f : ℝ → ℂ) :
    (∫ x in (0 : ℝ)..1, conj (f x)) = conj (∫ x in (0 : ℝ)..1, f x) := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  exact integral_conj

/-- Conditional reality: a formal total-derivative identity for
`k! (u P - ū σ(P))` makes `∫₀¹ u P` invariant under conjugation. -/
theorem integral_real_of_swap_exact38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (P : Poly) (k : ℕ) (ℓ : Poly)
    (hex : (k.factorial : Poly) *
        (MvPolynomial.X (false, 0) * P - MvPolynomial.X (true, 0) * jetSwapHom38 P) =
      spatialD ℓ) :
    conj (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (MvPolynomial.X (false, 0) * P)) =
      ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (MvPolynomial.X (false, 0) * P) := by
  set F : ℝ → ℂ := fun x => riccatiJetEvaluation u x (MvPolynomial.X (false, 0) * P) with hF
  have hswap : ∀ x, riccatiJetEvaluation u x
      (MvPolynomial.X (true, 0) * jetSwapHom38 P) = conj (F x) := by
    intro x
    have : MvPolynomial.X (true, 0) * jetSwapHom38 P =
        jetSwapHom38 (MvPolynomial.X (false, 0) * P) := by
      simp
    rw [this, riccatiJetEvaluation_swap38]
  have hFc : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (riccatiJetEvaluation_hasDerivAt u hu _ x).continuousAt
  have hconj : Continuous (fun x => (starRingEnd ℂ) (F x)) :=
    Complex.continuous_conj.comp hFc
  have hzero := riccatiJetEvaluation_integral_spatialD38 u hu hper ℓ
  rw [← hex] at hzero
  have hpt : ∀ x, riccatiJetEvaluation u x ((k.factorial : Poly) *
      (MvPolynomial.X (false, 0) * P - MvPolynomial.X (true, 0) * jetSwapHom38 P)) =
      (k.factorial : ℂ) * (F x - conj (F x)) := by
    intro x
    rw [← hswap x]
    simp [riccatiJetEvaluation, polynomialEvaluation, hF]
  simp_rw [hpt] at hzero
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hFc.intervalIntegrable _ _)
      (hconj.intervalIntegrable _ _),
    intervalIntegral_conj38] at hzero
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have := (mul_eq_zero.mp hzero).resolve_left hfac
  exact (sub_eq_zero.mp this).symm

/-- Conditional reality of the `j`-th local charge: under the formal
total-derivative identity at index `2j+1`, the imaginary part of
`∫₀¹ (-1)^{j+1} u p_{2j+1}` vanishes. -/
theorem formalChargeIntegrand_im_eq_zero_of_exact38 (j : ℕ) (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1) (ℓ : Poly)
    (hex : ((2 * j + 1).factorial : Poly) *
        (MvPolynomial.X (false, 0) * p (2 * j + 1) -
          MvPolynomial.X (true, 0) * jetSwapHom38 (p (2 * j + 1))) = spatialD ℓ) :
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalChargeIntegrand j)).im = 0 := by
  have hreal := integral_real_of_swap_exact38 u hu hper (p (2 * j + 1)) (2 * j + 1) ℓ hex
  have hI : (∫ x in (0 : ℝ)..1,
      riccatiJetEvaluation u x (MvPolynomial.X (false, 0) * p (2 * j + 1))).im = 0 :=
    Complex.conj_eq_iff_im.mp hreal
  have hpt : ∀ x, riccatiJetEvaluation u x (formalChargeIntegrand j) =
      (((-1 : ℤ) ^ (j + 1) : ℤ) : ℂ) *
        riccatiJetEvaluation u x (MvPolynomial.X (false, 0) * p (2 * j + 1)) := by
    intro x
    simp [formalChargeIntegrand, riccatiJetEvaluation, polynomialEvaluation, mul_assoc]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, Complex.mul_im, hI]
  rw [Complex.intCast_im]
  ring

end NlsGge.HierarchyRiccati.Core

end
