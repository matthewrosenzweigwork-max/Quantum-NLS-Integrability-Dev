import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB1Dual

/-! # Track B, step B2: the trace estimate `X^{0,c} ⊂ C_t L²` (`c > 1/2`) on the dense class

`denseNormSqE e s = Σ_k ∫ ⟨-2πξ + (2πk)²⟩^{e} |θ_k(ξ)|² dξ` (`θ_k = 𝓕⁻ s_k`) is the squared
`X^{0,e/2}` norm in the normalization of `denseNormSq` (`= denseNormSqE (2·13/32)`) and
`dualNormSq` (`= denseNormSqE (-2·13/32)`).

Main result `dense_trace_bound`: for `c > 1/2` there is one finite `C` with
`∫_𝕋 |v(t,x)|² dx ≤ C · denseNormSqE (2c) s` for every time `t` and every dense-class field.
Proof: torus Parseval; `|s_k(t)| ≤ ∫ |θ_k|` (the Fourier integral); weighted Cauchy–Schwarz;
`∫ ⟨-2πξ + λ⟩^{-2c} dξ = (2π)⁻¹ ∫ ⟨u⟩^{-2c} du < ∞` uniformly in `λ` (`2c > 1`).
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory SchwartzMap FourierTransform AddCircle
open scoped ENNReal ComplexConjugate

/-- The squared `X^{0,e/2}` norm of a dense-class field. -/
def denseNormSqE (e : ℝ) (s : ℤ → 𝓢(ℝ, ℂ)) : ℝ≥0∞ :=
  ∑' k : ℤ, ∫⁻ ξ, modWt e k (-(2 * Real.pi) * ξ) * ‖(𝓕⁻ (s k)) ξ‖ₑ ^ 2

theorem denseNormSq_eq_denseNormSqE (s : ℤ → 𝓢(ℝ, ℂ)) :
    denseNormSq s = denseNormSqE (2 * (13 / 32 : ℝ)) s := rfl

theorem dualNormSq_eq_denseNormSqE (s : ℤ → 𝓢(ℝ, ℂ)) :
    dualNormSq s = denseNormSqE (-(2 * (13 / 32 : ℝ))) s := rfl

/-- Torus Parseval for trigonometric polynomials, in `ℝ≥0∞`. -/
theorem lintegral_enorm_sq_torusPoly (S : Finset ℤ) (a : ℤ → ℂ) (ha : ∀ k ∉ S, a k = 0) :
    ∫⁻ x, ‖torusPoly S a x‖ₑ ^ 2 ∂haarAddCircle = ∑ k ∈ S, ‖a k‖ₑ ^ 2 := by
  have h := integral_conj_torusPoly_mul S a a ha
  have hl : ∀ x, conj (torusPoly S a x) * torusPoly S a x =
      ((‖torusPoly S a x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [Complex.conj_mul', Complex.ofReal_pow]
  have hr : ∀ k, conj (a k) * a k = ((‖a k‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [Complex.conj_mul', Complex.ofReal_pow]
  simp_rw [hl, hr] at h
  rw [integral_complex_ofReal, ← Complex.ofReal_sum] at h
  have h' := Complex.ofReal_injective h
  have hint : Integrable (fun x => ‖torusPoly S a x‖ ^ 2) haarAddCircle :=
    ((torusPoly S a).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc ∫⁻ x, ‖torusPoly S a x‖ₑ ^ 2 ∂haarAddCircle
      = ∫⁻ x, ENNReal.ofReal (‖torusPoly S a x‖ ^ 2) ∂haarAddCircle :=
        lintegral_congr fun x => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal (∫ x, ‖torusPoly S a x‖ ^ 2 ∂haarAddCircle) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by positivity)).symm
    _ = ∑ k ∈ S, ‖a k‖ₑ ^ 2 := by
        rw [h', ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Pointwise bound of a time-side Schwartz function by the `L¹` norm of its inverse transform. -/
theorem enorm_le_lintegral_enorm_fourierInv (s : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ‖s t‖ₑ ≤ ∫⁻ ξ, ‖(𝓕⁻ s : 𝓢(ℝ, ℂ)) ξ‖ₑ := by
  have hs : s t = 𝓕 (⇑(𝓕⁻ s : 𝓢(ℝ, ℂ))) t := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  have h1 : ‖s t‖ ≤ ∫ ξ, ‖(𝓕⁻ s : 𝓢(ℝ, ℂ)) ξ‖ := by
    rw [hs, Real.fourier_real_eq]
    refine (norm_integral_le_integral_norm _).trans
      (le_of_eq (integral_congr_ae (ae_of_all _ fun v => ?_)))
    simp only [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
  calc ‖s t‖ₑ = ENNReal.ofReal ‖s t‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (∫ ξ, ‖(𝓕⁻ s : 𝓢(ℝ, ℂ)) ξ‖) := ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ ξ, ‖(𝓕⁻ s : 𝓢(ℝ, ℂ)) ξ‖ₑ := by
        rw [ofReal_integral_eq_lintegral_ofReal (𝓕⁻ s).integrable.norm
          (ae_of_all _ fun ξ => norm_nonneg _)]
        exact lintegral_congr fun ξ => ofReal_norm _

/-- Weighted Cauchy–Schwarz: `(∫|θ|)² ≤ ∫ W^{-2e} · ∫ W^{2e}|θ|²`. -/
theorem sq_lintegral_enorm_le_weighted (e : ℝ) (k : ℤ) (θ : ℝ → ℂ) (hθ : Continuous θ) :
    (∫⁻ ξ, ‖θ ξ‖ₑ) ^ 2 ≤ (∫⁻ ξ, modWt (-(2 * e)) k (-(2 * Real.pi) * ξ)) *
      ∫⁻ ξ, modWt (2 * e) k (-(2 * Real.pi) * ξ) * ‖θ ξ‖ₑ ^ 2 := by
  have hW : Measurable fun ξ : ℝ => modWt e k (-(2 * Real.pi) * ξ) :=
    (measurable_modWt e k).comp (measurable_const.mul measurable_id)
  have hV : Measurable fun ξ : ℝ => modWt (-e) k (-(2 * Real.pi) * ξ) :=
    (measurable_modWt (-e) k).comp (measurable_const.mul measurable_id)
  have hθm : Measurable fun ξ => ‖θ ξ‖ₑ := hθ.measurable.enorm
  have hsplit : ∀ ξ, ‖θ ξ‖ₑ = modWt (-e) k (-(2 * Real.pi) * ξ) *
      (modWt e k (-(2 * Real.pi) * ξ) * ‖θ ξ‖ₑ) := fun ξ => by
    rw [← mul_assoc, modWt_neg_mul, one_mul]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hV.aemeasurable (hW.mul hθm).aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  have e1 : ∀ ξ, modWt (-e) k (-(2 * Real.pi) * ξ) ^ 2 = modWt (-(2 * e)) k (-(2 * Real.pi) * ξ) :=
    fun ξ => by rw [modWt_sq, mul_neg]
  have e2 : ∀ ξ, (modWt e k (-(2 * Real.pi) * ξ) * ‖θ ξ‖ₑ) ^ 2 =
      modWt (2 * e) k (-(2 * Real.pi) * ξ) * ‖θ ξ‖ₑ ^ 2 := fun ξ => by rw [mul_pow, modWt_sq]
  simp_rw [e1, e2, ← hsplit] at h
  calc (∫⁻ ξ, ‖θ ξ‖ₑ) ^ 2
      ≤ ((∫⁻ ξ, modWt (-(2 * e)) k (-(2 * Real.pi) * ξ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ ξ, modWt (2 * e) k (-(2 * Real.pi) * ξ) * ‖θ ξ‖ₑ ^ 2) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ bot_le h 2
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

/-- The reciprocal-weight integral is finite and independent of the mode. -/
theorem lintegral_modWt_neg_eq (c : ℝ) (k : ℤ) :
    ∫⁻ ξ, modWt (-(2 * c)) k (-(2 * Real.pi) * ξ) =
      ENNReal.ofReal |(-(2 * Real.pi))⁻¹| * ∫⁻ u, ‖brk u ^ (-(2 * c))‖ₑ := by
  have hc : -(2 * Real.pi) ≠ 0 := by have := Real.pi_pos; linarith
  rw [lintegral_comp_mul_left_real (modWt (-(2 * c)) k) hc]
  congr 1
  refine (lintegral_congr fun u => ?_).trans
    (lintegral_add_right_eq_self (fun u => ‖brk u ^ (-(2 * c))‖ₑ) ((2 * Real.pi * k) ^ 2))
  show modWt (-(2 * c)) k u = ‖brk (u + (2 * Real.pi * k) ^ 2) ^ (-(2 * c))‖ₑ
  rw [modWt, Real.enorm_eq_ofReal (brk_rpow_nonneg _ _)]

/-- **Trace estimate on the dense class** (`c > 1/2`): `sup_t ‖v(t)‖²_{L²(𝕋)} ≤ C ‖v‖²_{X^{0,c}}`. -/
theorem dense_trace_bound {c : ℝ} (hc : 1 / 2 < c) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (S : Finset ℤ) (s : ℤ → 𝓢(ℝ, ℂ)), (∀ k ∉ S, s k = 0) → ∀ t : ℝ,
      ∫⁻ x, ‖denseField S s t x‖ₑ ^ 2 ∂haarAddCircle ≤ C * denseNormSqE (2 * c) s := by
  set B : ℝ≥0∞ := ENNReal.ofReal |(-(2 * Real.pi))⁻¹| * ∫⁻ u, ‖brk u ^ (-(2 * c))‖ₑ with hB
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (integrable_brk_rpow (by linarith : 1 < 2 * c)).hasFiniteIntegral.ne
  refine ⟨B, hBt, fun S s hs t => ?_⟩
  have hmode : ∀ k, ‖s k t‖ₑ ^ 2 ≤
      B * ∫⁻ ξ, modWt (2 * c) k (-(2 * Real.pi) * ξ) * ‖(𝓕⁻ (s k)) ξ‖ₑ ^ 2 := fun k => by
    calc ‖s k t‖ₑ ^ 2 ≤ (∫⁻ ξ, ‖(𝓕⁻ (s k)) ξ‖ₑ) ^ 2 :=
          pow_le_pow_left₀ bot_le (enorm_le_lintegral_enorm_fourierInv (s k) t) 2
      _ ≤ _ := by
          rw [hB, ← lintegral_modWt_neg_eq c k]
          exact sq_lintegral_enorm_le_weighted c k _ (𝓕⁻ (s k)).continuous
  have hs' : ∀ k ∉ S, (fun k => s k t) k = 0 := fun k hk => by simp [hs k hk]
  calc ∫⁻ x, ‖denseField S s t x‖ₑ ^ 2 ∂haarAddCircle = ∑ k ∈ S, ‖s k t‖ₑ ^ 2 :=
        lintegral_enorm_sq_torusPoly S (fun k => s k t) hs'
    _ ≤ ∑ k ∈ S, B * ∫⁻ ξ, modWt (2 * c) k (-(2 * Real.pi) * ξ) * ‖(𝓕⁻ (s k)) ξ‖ₑ ^ 2 :=
        Finset.sum_le_sum fun k _ => hmode k
    _ = B * ∑ k ∈ S, ∫⁻ ξ, modWt (2 * c) k (-(2 * Real.pi) * ξ) * ‖(𝓕⁻ (s k)) ξ‖ₑ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ B * denseNormSqE (2 * c) s := by
        gcongr
        exact ENNReal.sum_le_tsum _

end LiebLiniger.FixedPeriod.ALLS.PdeB
