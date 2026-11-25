import NlsGge.Hierarchy.RiccatiLocalChargeReal38
import NlsGge.Hierarchy.RiccatiMonomialPeriodicIBPStepRecoveryThird
import Mathlib.Tactic

/-! Batch 38, E06.06 (formal-coefficient side of S5): the coefficients
`b_m = i (-2)^{-m} ∫₀¹ u p_m` of the expansion of `i∫₀¹ uΓ_η` at `ζ = iη`
(formal variable `z = 1/(2iζ) = -1/(2η)`), their relation to the local charges
(odd `m = 2j+1`: `b_{2j+1} = i(-1)^j 2^{-2j-1} Q_{2j}`), and reality of the
even coefficients. The interface with the spectral side (E02 thread) is
`k(iη) = iη + Σ_{m≤K} b_m η^{-m} + O(η^{-K-1})`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory
open scoped ContDiff ComplexConjugate

/-- `b_m = i (-2)^{-m} ∫₀¹ u p_m` (`b_0 = 0` since `p 0 = 0`). -/
def riccatiQuasiCoeff38 (u : ℝ → ℂ) (m : ℕ) : ℂ :=
  Complex.I * ((-2 : ℂ) ^ m)⁻¹ *
    ∫ x in (0:ℝ)..1, riccatiJetEvaluation u x (MvPolynomial.X (false, 0) * p m)

theorem riccatiJetEvaluation_X_mul38 (u : ℝ → ℂ) (x : ℝ) (P : Poly) :
    riccatiJetEvaluation u x (MvPolynomial.X (false, 0) * P) =
      u x * riccatiJetEvaluation u x P := by
  simp [riccatiJetEvaluation, riccatiJetFunction]

/-- Integrating the uniform asymptotic expansion of `Γ` against `u`. -/
theorem riccati_integral_expansion_of_asymptotic38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (K : ℕ) (η C U : ℝ) (_hη : 0 < η) (hU : ∀ x ∈ Set.Icc (0:ℝ) 1, ‖u x‖ ≤ U)
    (Γ : ℝ → ℂ) (hΓc : Continuous Γ)
    (hasym : ∀ x, ‖Γ x - ∑ k ∈ Finset.range (K + 1),
      riccatiJetEvaluation u x (p k) * ((-2 * η : ℂ))⁻¹ ^ k‖ ≤ C * η⁻¹ ^ (K + 1)) :
    ‖Complex.I * (∫ x in (0:ℝ)..1, u x * Γ x) -
        ∑ m ∈ Finset.range (K + 1), riccatiQuasiCoeff38 u m * (η : ℂ)⁻¹ ^ m‖ ≤
      U * (C * η⁻¹ ^ (K + 1)) := by
  set G : ℝ → ℂ := fun x => ∑ k ∈ Finset.range (K + 1),
    riccatiJetEvaluation u x (p k) * ((-2 * η : ℂ))⁻¹ ^ k with hG
  have hGc : Continuous G := by
    rw [hG]
    exact continuous_finsetSum _ (fun k _ =>
      (riccatiJetEvaluation_continuousNativeRecovery u hu (p k)).mul continuous_const)
  have huc : Continuous u := hu.continuous
  have hsum : (∑ m ∈ Finset.range (K + 1), riccatiQuasiCoeff38 u m * (η : ℂ)⁻¹ ^ m) =
      Complex.I * ∫ x in (0:ℝ)..1, u x * G x := by
    rw [hG]
    simp_rw [Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum (fun k _ => by
      apply Continuous.intervalIntegrable
      exact huc.mul ((riccatiJetEvaluation_continuousNativeRecovery u hu (p k)).mul
        continuous_const)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    unfold riccatiQuasiCoeff38
    simp_rw [riccatiJetEvaluation_X_mul38]
    have hmul : (∫ x in (0:ℝ)..1, u x * (riccatiJetEvaluation u x (p m) * (-2 * (η:ℂ))⁻¹ ^ m)) =
        (∫ x in (0:ℝ)..1, u x * riccatiJetEvaluation u x (p m)) * (-2 * (η:ℂ))⁻¹ ^ m := by
      rw [← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr
      intro x _
      simp only
      ring
    rw [hmul]
    simp only [mul_inv, mul_pow, inv_pow]
    ring
  rw [hsum, ← mul_sub, ← intervalIntegral.integral_sub (f := fun x => u x * Γ x)
    (g := fun x => u x * G x)
    ((huc.mul hΓc).intervalIntegrable _ _) ((huc.mul hGc).intervalIntegrable _ _)]
  rw [norm_mul, Complex.norm_I, one_mul]
  have hb : ∀ x ∈ Set.uIoc (0:ℝ) 1, ‖u x * Γ x - u x * G x‖ ≤ U * (C * η⁻¹ ^ (K + 1)) := by
    intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    rw [← mul_sub, norm_mul]
    have hUx := hU x ⟨hx.1.le, hx.2⟩
    have hUnn : 0 ≤ U := (norm_nonneg _).trans hUx
    exact mul_le_mul hUx (hasym x) (norm_nonneg _) hUnn
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

/-- Odd coefficients are the local charges: `b_{2j+1} = i(-1)^j 2^{-2j-1} Q_{2j}`. -/
theorem riccatiQuasiCoeff38_odd (u : ℝ → ℂ) (j : ℕ) :
    riccatiQuasiCoeff38 u (2 * j + 1) =
      Complex.I * (-1 : ℂ) ^ j * ((2 : ℂ) ^ (2 * j + 1))⁻¹ *
        ∫ x in (0:ℝ)..1, riccatiJetEvaluation u x (formalChargeIntegrand j) := by
  unfold riccatiQuasiCoeff38
  have hpt : ∀ x, riccatiJetEvaluation u x (formalChargeIntegrand j) =
      (-1 : ℂ) ^ (j + 1) *
        riccatiJetEvaluation u x (MvPolynomial.X (false, 0) * p (2 * j + 1)) := by
    intro x
    simp [formalChargeIntegrand, riccatiJetEvaluation, polynomialEvaluation, mul_assoc]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  have h2 : ((-2 : ℂ) ^ (2 * j + 1)) = -(2 : ℂ) ^ (2 * j + 1) := by
    rw [show (-2 : ℂ) = (-1) * 2 by norm_num, mul_pow, pow_succ, pow_mul]; norm_num
  rw [h2, inv_neg]
  have h1 : ((-1 : ℂ) ^ j) * ((-1 : ℂ) ^ (j + 1)) = -1 := by
    rw [← pow_add, show j + (j + 1) = 2 * j + 1 by ring, pow_succ, pow_mul]; norm_num
  linear_combination (-(Complex.I * ((2 : ℂ) ^ (2 * j + 1))⁻¹ *
    ∫ x in (0:ℝ)..1, riccatiJetEvaluation u x (MvPolynomial.X (false, 0) * p (2 * j + 1)))) * h1

/-- Even coefficients of `uΓ + ūΔ`: `k!(u p_k + ū σ(p_k))` is a total derivative. -/
theorem riccatiEvenCoefficient_exact38 (k : ℕ) (hk : Even k) :
    ∃ ℓ : Poly, (k.factorial : Poly) *
      (MvPolynomial.X (false, 0) * p k +
        MvPolynomial.X (true, 0) * jetSwapHom38 (p k)) = spatialD ℓ := by
  have hP : PowerSeries.constantCoeff (riccatiGamma38 * riccatiDelta38) = 0 := by
    rw [map_mul]
    have h0 : PowerSeries.constantCoeff riccatiGamma38 = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, riccatiGamma38,
        PowerSeries.coeff_mk]
      simp [p]
    rw [h0, zero_mul]
  obtain ⟨ℓ, hℓ⟩ := formalLog_exact38 spatialD
    (PowerSeries.C (MvPolynomial.X (false, 0)) * riccatiGamma38 +
      PowerSeries.C (MvPolynomial.X (true, 0)) * riccatiDelta38)
    (riccatiGamma38 * riccatiDelta38) hP riccatiWronskian38 k
  refine ⟨ℓ, Eq.trans ?_ hℓ⟩
  congr 1
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, riccatiGamma38,
    riccatiDelta38, PowerSeries.coeff_mk, PowerSeries.coeff_mk, hk.neg_one_pow, one_mul]
  rfl

/-- The even integrals `∫₀¹ u p_{2j}` are purely imaginary. -/
theorem riccatiEvenIntegral_re_eq_zero38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (j : ℕ) :
    (∫ x in (0:ℝ)..1,
      riccatiJetEvaluation u x (MvPolynomial.X (false, 0) * p (2 * j))).re = 0 := by
  obtain ⟨ℓ, hex⟩ := riccatiEvenCoefficient_exact38 (2 * j) (even_two_mul j)
  set P := p (2 * j)
  set F : ℝ → ℂ := fun x => riccatiJetEvaluation u x (MvPolynomial.X (false, 0) * P) with hF
  have hswap : ∀ x, riccatiJetEvaluation u x
      (MvPolynomial.X (true, 0) * jetSwapHom38 P) = conj (F x) := by
    intro x
    have : MvPolynomial.X (true, 0) * jetSwapHom38 P =
        jetSwapHom38 (MvPolynomial.X (false, 0) * P) := by simp
    rw [this, riccatiJetEvaluation_swap38]
  have hFc : Continuous F := riccatiJetEvaluation_continuousNativeRecovery u hu _
  have hconj : Continuous (fun x => (starRingEnd ℂ) (F x)) := Complex.continuous_conj.comp hFc
  have hzero := riccatiJetEvaluation_integral_spatialD38 u hu hper ℓ
  rw [← hex] at hzero
  have hpt : ∀ x, riccatiJetEvaluation u x (((2 * j).factorial : Poly) *
      (MvPolynomial.X (false, 0) * P + MvPolynomial.X (true, 0) * jetSwapHom38 P)) =
      ((2 * j).factorial : ℂ) * (F x + conj (F x)) := by
    intro x
    rw [← hswap x]
    simp [riccatiJetEvaluation, polynomialEvaluation, hF]
  simp_rw [hpt] at hzero
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hFc.intervalIntegrable _ _) (hconj.intervalIntegrable _ _),
    intervalIntegral_conj38] at hzero
  have hfac : ((2 * j).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h := (mul_eq_zero.mp hzero).resolve_left hfac
  have hre := congrArg Complex.re h
  rw [Complex.add_re, Complex.conj_re, Complex.zero_re] at hre
  linarith

/-- The even coefficients `b_{2j}` are real. -/
theorem riccatiQuasiCoeff38_even_im (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (j : ℕ) :
    (riccatiQuasiCoeff38 u (2 * j)).im = 0 := by
  unfold riccatiQuasiCoeff38
  set r : ℝ := ((4 : ℝ) ^ j)⁻¹
  have h4 : ((-2 : ℂ) ^ (2 * j))⁻¹ = (r : ℂ) := by
    simp only [r, pow_mul]; push_cast; norm_num
  have hW := riccatiEvenIntegral_re_eq_zero38 u hu hper j
  rw [h4]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, hW]
  ring

/-- The odd coefficients `b_{2j+1}` are purely imaginary (the charges are real). -/
theorem riccatiQuasiCoeff38_odd_re (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (j : ℕ) :
    (riccatiQuasiCoeff38 u (2 * j + 1)).re = 0 := by
  rw [riccatiQuasiCoeff38_odd, formalChargeIntegrand_integral_eq_re38 j u hu hper]
  set r : ℝ := (-1 : ℝ) ^ j * ((2 : ℝ) ^ (2 * j + 1))⁻¹
  set q : ℝ := (∫ x in (0:ℝ)..1, riccatiJetEvaluation u x (formalChargeIntegrand j)).re
  have : Complex.I * (-1 : ℂ) ^ j * ((2 : ℂ) ^ (2 * j + 1))⁻¹ = Complex.I * (r : ℂ) := by
    simp only [r]; push_cast; ring
  rw [this]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

theorem riccatiQuasiCoeff38_zero (u : ℝ → ℂ) : riccatiQuasiCoeff38 u 0 = 0 := by
  have hp0 : p 0 = 0 := by simp [p]
  simp [riccatiQuasiCoeff38, hp0, riccatiJetEvaluation]

theorem sum_range_succ_eq_Icc38 {M : Type*} [AddCommMonoid M] (f : ℕ → M) (hf : f 0 = 0)
    (K : ℕ) : ∑ k ∈ Finset.range (K + 1), f k = ∑ k ∈ Finset.Icc 1 K, f k := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos K), hf, zero_add]
  rfl

/-- Interface form (agreed with the E02 thread): sums over `m ∈ Icc 1 K`
(`b_0 = 0`, `p 0 = 0`) and the constant `U ≥ sup_{[0,1]} ‖u‖` explicit. -/
theorem riccati_integral_expansion_Icc38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (K : ℕ) (η C U : ℝ) (hη : 0 < η) (hU : ∀ x ∈ Set.Icc (0:ℝ) 1, ‖u x‖ ≤ U)
    (Γ : ℝ → ℂ) (hΓc : Continuous Γ)
    (hasym : ∀ x, ‖Γ x - ∑ k ∈ Finset.Icc 1 K,
      riccatiJetEvaluation u x (p k) * ((-2 * η : ℂ))⁻¹ ^ k‖ ≤ C * η⁻¹ ^ (K + 1)) :
    ‖Complex.I * (∫ x in (0:ℝ)..1, u x * Γ x) -
        ∑ m ∈ Finset.Icc 1 K, riccatiQuasiCoeff38 u m * (η : ℂ)⁻¹ ^ m‖ ≤
      U * (C * η⁻¹ ^ (K + 1)) := by
  have hp0 : p 0 = 0 := by simp [p]
  rw [← sum_range_succ_eq_Icc38 (fun m => riccatiQuasiCoeff38 u m * (η : ℂ)⁻¹ ^ m)
    (by simp [riccatiQuasiCoeff38_zero])]
  refine riccati_integral_expansion_of_asymptotic38 u hu K η C U hη hU Γ hΓc (fun x => ?_)
  rw [sum_range_succ_eq_Icc38 (fun k => riccatiJetEvaluation u x (p k) * ((-2 * η : ℂ))⁻¹ ^ k)
    (by simp [hp0, riccatiJetEvaluation])]
  exact hasym x

end NlsGge.HierarchyRiccati.Core

end
