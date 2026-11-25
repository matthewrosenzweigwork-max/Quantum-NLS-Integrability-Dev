import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB2Trace

/-! # Track B, step B2: real-variable core of the cutoff gain

Abstract ingredients of the estimate `‖η(·/δ) w‖_{H^{-β}} ≤ C δ^{β-α} ‖w‖_{H^{-α}}`
(`0 ≤ α ≤ β < 1/2`, `0 < δ ≤ 1`), proved directly in the negative-exponent direction (no duality):

* `lintegral_sq_conv_le`: weighted Cauchy–Schwarz/Schur bound
  `∫ m(x)² (∫ R(x-y) g(y) dy)² dx ≤ (∫R) · B · ∫ g²` whenever `∫ m(x)² R(x-y) dx ≤ B` for all `y`;
* `brk_add_le`: `⟨a+b⟩ ≤ ⟨a⟩ + |b|`;
* `brk_rpow_le_kernel`: `⟨q⟩^α ≤ δ^{-α} (1 + δ⟨p⟩)^α (1 + δ|q-p|)^α`.
All lower integrals are over Lebesgue measure on `ℝ`, in `ℝ≥0∞`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory
open scoped ENNReal

/-- Cauchy–Schwarz for a translated kernel: `(∫ R(x-y) g y)² ≤ (∫ R) · ∫ R(x-y) g(y)²`. -/
theorem sq_lintegral_kernel_le (R g : ℝ → ℝ≥0∞) (hR : Measurable R) (hg : Measurable g) (x : ℝ) :
    (∫⁻ y, R (x - y) * g y) ^ 2 ≤ (∫⁻ y, R y) * ∫⁻ y, R (x - y) * g y ^ 2 := by
  have hRx : Measurable fun y => R (x - y) := hR.comp (measurable_const.sub measurable_id)
  have hf : Measurable fun y => R (x - y) ^ (1 / 2 : ℝ) := hRx.pow_const _
  have hh : Measurable fun y => R (x - y) ^ (1 / 2 : ℝ) * g y := hf.mul hg
  have hsq : ∀ r : ℝ≥0∞, (r ^ (1 / 2 : ℝ)) ^ 2 = r := fun r => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hf.aemeasurable hh.aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  have e1 : ∀ y, R (x - y) ^ (1 / 2 : ℝ) * (R (x - y) ^ (1 / 2 : ℝ) * g y) = R (x - y) * g y :=
    fun y => by rw [← mul_assoc, ← sq, hsq]
  have e2 : ∀ y, (R (x - y) ^ (1 / 2 : ℝ) * g y) ^ 2 = R (x - y) * g y ^ 2 :=
    fun y => by rw [mul_pow, hsq]
  simp_rw [e1, e2, hsq] at h
  rw [lintegral_sub_left_eq_self R x] at h
  calc (∫⁻ y, R (x - y) * g y) ^ 2
      ≤ ((∫⁻ y, R y) ^ (1 / (2 : ℝ)) * (∫⁻ y, R (x - y) * g y ^ 2) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ bot_le h 2
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

/-- **Weighted Schur bound.** If `∫ m(x)² R(x-y) dx ≤ B` for every `y`, then
`∫ m(x)² (∫ R(x-y) g(y) dy)² dx ≤ (∫ R) · B · ∫ g²`. -/
theorem lintegral_sq_conv_le (m R g : ℝ → ℝ≥0∞) (hm : Measurable m) (hR : Measurable R)
    (hg : Measurable g) (B : ℝ≥0∞) (hB : ∀ y, ∫⁻ x, m x ^ 2 * R (x - y) ≤ B) :
    ∫⁻ x, m x ^ 2 * (∫⁻ y, R (x - y) * g y) ^ 2 ≤ (∫⁻ y, R y) * B * ∫⁻ y, g y ^ 2 := by
  have hF : Measurable (Function.uncurry fun x y => m x ^ 2 * (R (x - y) * g y ^ 2)) :=
    (hm.comp measurable_fst).pow_const 2 |>.mul
      ((hR.comp (measurable_fst.sub measurable_snd)).mul ((hg.comp measurable_snd).pow_const 2))
  have hin : ∀ x, Measurable fun y => R (x - y) * g y ^ 2 := fun x =>
    (hR.comp (measurable_const.sub measurable_id)).mul (hg.pow_const 2)
  have hJ : Measurable fun x => ∫⁻ y, m x ^ 2 * (R (x - y) * g y ^ 2) :=
    hF.lintegral_prod_right'
  calc ∫⁻ x, m x ^ 2 * (∫⁻ y, R (x - y) * g y) ^ 2
      ≤ ∫⁻ x, m x ^ 2 * ((∫⁻ y, R y) * ∫⁻ y, R (x - y) * g y ^ 2) :=
        lintegral_mono fun x => by
          gcongr
          exact sq_lintegral_kernel_le R g hR hg x
    _ = (∫⁻ y, R y) * ∫⁻ x, ∫⁻ y, m x ^ 2 * (R (x - y) * g y ^ 2) := by
        rw [← lintegral_const_mul _ hJ]
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul _ (hin x)]
        ring
    _ = (∫⁻ y, R y) * ∫⁻ y, ∫⁻ x, m x ^ 2 * (R (x - y) * g y ^ 2) := by
        rw [lintegral_lintegral_swap hF.aemeasurable]
    _ ≤ (∫⁻ y, R y) * ∫⁻ y, B * g y ^ 2 := by
        gcongr with y
        calc ∫⁻ x, m x ^ 2 * (R (x - y) * g y ^ 2) = (∫⁻ x, m x ^ 2 * R (x - y)) * g y ^ 2 := by
              have hm2 : Measurable fun x => m x ^ 2 * R (x - y) :=
                (hm.pow_const 2).mul (hR.comp (measurable_id.sub measurable_const))
              rw [← lintegral_mul_const _ hm2]
              refine lintegral_congr fun x => ?_
              ring
          _ ≤ B * g y ^ 2 := by
              gcongr
              exact hB y
    _ = _ := by rw [lintegral_const_mul _ (hg.pow_const 2), mul_assoc]

/-- `⟨a + b⟩ ≤ ⟨a⟩ + |b|`. -/
theorem brk_add_le (a b : ℝ) : brk (a + b) ≤ brk a + |b| := by
  have h1 := brk_sq a
  have h2 := abs_le_brk a
  have h3 : a * b ≤ brk a * |b| := by
    calc a * b ≤ |a * b| := le_abs_self _
      _ = |a| * |b| := abs_mul a b
      _ ≤ brk a * |b| := mul_le_mul_of_nonneg_right h2 (abs_nonneg b)
  have h4 : 0 ≤ brk a + |b| := add_nonneg (brk_pos a).le (abs_nonneg b)
  rw [brk, Real.sqrt_le_iff]
  refine ⟨h4, ?_⟩
  have h5 : |b| ^ 2 = b ^ 2 := sq_abs b
  nlinarith

/-- Kernel majorization: for `0 < δ`, `0 ≤ α`,
`⟨q⟩^α ≤ δ^{-α} (1 + δ⟨p⟩)^α (1 + δ|q-p|)^α`. -/
theorem brk_rpow_le_kernel {δ α : ℝ} (hδ : 0 < δ) (hα : 0 ≤ α) (p q : ℝ) :
    brk q ^ α ≤ δ ^ (-α) * ((1 + δ * brk p) ^ α * (1 + δ * |q - p|) ^ α) := by
  have hq : brk q ≤ brk p + |q - p| := by
    have := brk_add_le p (q - p)
    rwa [add_sub_cancel] at this
  have hprod : δ * brk q ≤ (1 + δ * brk p) * (1 + δ * |q - p|) := by
    have hb := (brk_pos p).le
    have ha := abs_nonneg (q - p)
    have : δ * brk q ≤ δ * brk p + δ * |q - p| := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hδ.le hb) (mul_nonneg hδ.le ha)]
  have hpow := Real.rpow_le_rpow (mul_nonneg hδ.le (brk_pos q).le) hprod hα
  rw [Real.mul_rpow hδ.le (brk_pos q).le,
    Real.mul_rpow (add_nonneg zero_le_one (mul_nonneg hδ.le (brk_pos p).le))
      (add_nonneg zero_le_one (mul_nonneg hδ.le (abs_nonneg _)))] at hpow
  rw [← mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos hδ α), ← mul_assoc,
    ← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero, one_mul]
  exact hpow

end LiebLiniger.FixedPeriod.ALLS.PdeB
