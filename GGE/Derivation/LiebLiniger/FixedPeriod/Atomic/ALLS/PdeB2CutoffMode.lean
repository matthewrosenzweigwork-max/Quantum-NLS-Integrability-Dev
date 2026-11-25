import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB2CutoffWeight

/-! # Track B, step B2: the cutoff gain for one spatial mode (kernel form)

For a convolution kernel `κ` dominated at scale `δ` by an integrable, bounded profile `R₁`:
`|κ(r)| (1 + δ|2πr|)^α ≤ δ R₁(δr)`, and any measurable `θ`,
`∫ ⟨-2πξ+(2πk)²⟩^{-2β} (∫ |κ(ξ-ζ)| |θ(ζ)| dζ)² dξ ≤ C δ^{2β-2α} ∫ ⟨-2πζ+(2πk)²⟩^{-2α} |θ(ζ)|² dζ`
(`0 ≤ α ≤ β`, `0 < β < 1/2`, `δ > 0`), with `C = 2^{2α} (∫R₁) (A₀ K₁ + ∫R₁)` independent of `δ` and `k`.
This is the `H^{-α} → H^{-β}` cutoff gain in the negative direction, proved directly (no duality,
hence no conjugate/real-cutoff issue): kernel majorization, the weighted Schur bound and the uniform
weight integral. For `κ = 𝓕⁻(η(·/δ))`, `|κ(r)| = δ|𝓕⁻η(δr)|` gives the hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory
open scoped ENNReal

theorem modWt_ne_top (e : ℝ) (k : ℤ) (t : ℝ) : modWt e k t ≠ ⊤ := ENNReal.ofReal_ne_top

/-- Pointwise kernel majorization in the modulation weights. -/
theorem modWt_kernel_le {α β δ : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (R1 : ℝ → ℝ≥0∞) (κ : ℝ → ℂ)
    (hκ : ∀ r, ‖κ r‖ₑ * ENNReal.ofReal ((1 + δ * |2 * Real.pi * r|) ^ α) ≤
      ENNReal.ofReal δ * R1 (δ * r)) (k : ℤ) (ξ ζ : ℝ) :
    modWt (-β) k (-(2 * Real.pi) * ξ) * ‖κ (ξ - ζ)‖ₑ * modWt α k (-(2 * Real.pi) * ζ) ≤
      ENNReal.ofReal (δ ^ (-α)) *
        ENNReal.ofReal (brk (-(2 * Real.pi) * ξ + (2 * Real.pi * k) ^ 2) ^ (-β) *
          (1 + δ * brk (-(2 * Real.pi) * ξ + (2 * Real.pi * k) ^ 2)) ^ α) *
        (ENNReal.ofReal δ * R1 (δ * (ξ - ζ))) := by
  set p := -(2 * Real.pi) * ξ + (2 * Real.pi * k) ^ 2 with hp
  set q := -(2 * Real.pi) * ζ + (2 * Real.pi * k) ^ 2 with hq
  have h1 := brk_rpow_le_kernel (p := p) (q := q) hδ hα
  have hqp : q - p = 2 * Real.pi * (ξ - ζ) := by rw [hp, hq]; ring
  rw [hqp] at h1
  have hA : (0 : ℝ) ≤ (1 + δ * brk p) ^ α :=
    Real.rpow_nonneg (add_nonneg zero_le_one (mul_nonneg hδ.le (brk_pos _).le)) _
  have hB : (0 : ℝ) ≤ (1 + δ * |2 * Real.pi * (ξ - ζ)|) ^ α :=
    Real.rpow_nonneg (add_nonneg zero_le_one (mul_nonneg hδ.le (abs_nonneg _))) _
  have hW : modWt α k (-(2 * Real.pi) * ζ) ≤ ENNReal.ofReal (δ ^ (-α)) *
      (ENNReal.ofReal ((1 + δ * brk p) ^ α) *
        ENNReal.ofReal ((1 + δ * |2 * Real.pi * (ξ - ζ)|) ^ α)) := by
    rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
    exact ENNReal.ofReal_le_ofReal h1
  have hm : modWt (-β) k (-(2 * Real.pi) * ξ) * ENNReal.ofReal ((1 + δ * brk p) ^ α) =
      ENNReal.ofReal (brk p ^ (-β) * (1 + δ * brk p) ^ α) := by
    rw [modWt, ENNReal.ofReal_mul (brk_rpow_nonneg _ _)]
  calc modWt (-β) k (-(2 * Real.pi) * ξ) * ‖κ (ξ - ζ)‖ₑ * modWt α k (-(2 * Real.pi) * ζ)
      ≤ modWt (-β) k (-(2 * Real.pi) * ξ) * ‖κ (ξ - ζ)‖ₑ * (ENNReal.ofReal (δ ^ (-α)) *
          (ENNReal.ofReal ((1 + δ * brk p) ^ α) *
            ENNReal.ofReal ((1 + δ * |2 * Real.pi * (ξ - ζ)|) ^ α))) := by gcongr
    _ = ENNReal.ofReal (δ ^ (-α)) *
          (modWt (-β) k (-(2 * Real.pi) * ξ) * ENNReal.ofReal ((1 + δ * brk p) ^ α)) *
          (‖κ (ξ - ζ)‖ₑ * ENNReal.ofReal ((1 + δ * |2 * Real.pi * (ξ - ζ)|) ^ α)) := by ring
    _ ≤ _ := by
        rw [hm]
        exact mul_le_mul' le_rfl (hκ (ξ - ζ))

/-- **Cutoff gain for one mode, kernel form.** -/
theorem cutoff_gain_mode {α β δ : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ0 : 0 < β) (hβ : β < 1 / 2)
    (hδ : 0 < δ) (R1 : ℝ → ℝ≥0∞) (hR1 : Measurable R1) (A0 : ℝ≥0∞) (hA0 : A0 ≠ ⊤)
    (hRA : ∀ u, R1 u ≤ A0) (κ θ : ℝ → ℂ) (hθ : Measurable θ)
    (hκ : ∀ r, ‖κ r‖ₑ * ENNReal.ofReal ((1 + δ * |2 * Real.pi * r|) ^ α) ≤
      ENNReal.ofReal δ * R1 (δ * r)) (k : ℤ) :
    ∫⁻ ξ, modWt (-(2 * β)) k (-(2 * Real.pi) * ξ) * (∫⁻ ζ, ‖κ (ξ - ζ)‖ₑ * ‖θ ζ‖ₑ) ^ 2 ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) * (∫⁻ u, R1 u) *
        (A0 * ENNReal.ofReal (|(-(2 * Real.pi))⁻¹| * (2 / (1 - 2 * β))) + ∫⁻ u, R1 u) *
        ENNReal.ofReal (δ ^ (2 * β - 2 * α)) *
        ∫⁻ ζ, modWt (-(2 * α)) k (-(2 * Real.pi) * ζ) * ‖θ ζ‖ₑ ^ 2 := by
  set lam : ℝ := (2 * Real.pi * k) ^ 2 with hlam
  set m : ℝ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (brk (-(2 * Real.pi) * ξ + lam) ^ (-β) *
    (1 + δ * brk (-(2 * Real.pi) * ξ + lam)) ^ α) with hmdef
  set R : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal δ * R1 (δ * r) with hRdef
  set g : ℝ → ℝ≥0∞ := fun ζ => modWt (-α) k (-(2 * Real.pi) * ζ) * ‖θ ζ‖ₑ with hgdef
  have haff : Measurable fun ξ : ℝ => -(2 * Real.pi) * ξ + lam :=
    (measurable_const.mul measurable_id).add measurable_const
  have hmm : Measurable m := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact ((continuous_brk_rpow _).measurable.comp haff).mul
      (((measurable_const.add (measurable_const.mul (continuous_brk.measurable.comp haff)))).pow_const _)
  have hRm : Measurable R := measurable_const.mul (hR1.comp (measurable_const.mul measurable_id))
  have hgm : Measurable g :=
    ((measurable_modWt (-α) k).comp (measurable_const.mul measurable_id)).mul hθ.enorm
  -- pointwise in ξ
  have hx : ∀ ξ, modWt (-(2 * β)) k (-(2 * Real.pi) * ξ) * (∫⁻ ζ, ‖κ (ξ - ζ)‖ₑ * ‖θ ζ‖ₑ) ^ 2 ≤
      ENNReal.ofReal (δ ^ (-α)) ^ 2 * (m ξ ^ 2 * (∫⁻ ζ, R (ξ - ζ) * g ζ) ^ 2) := by
    intro ξ
    have e1 : modWt (-(2 * β)) k (-(2 * Real.pi) * ξ) = modWt (-β) k (-(2 * Real.pi) * ξ) ^ 2 := by
      rw [modWt_sq, mul_neg]
    rw [e1, ← mul_pow, ← lintegral_const_mul' _ _ (modWt_ne_top _ _ _)]
    calc (∫⁻ ζ, modWt (-β) k (-(2 * Real.pi) * ξ) * (‖κ (ξ - ζ)‖ₑ * ‖θ ζ‖ₑ)) ^ 2
        ≤ (∫⁻ ζ, (ENNReal.ofReal (δ ^ (-α)) * m ξ) * (R (ξ - ζ) * g ζ)) ^ 2 := by
          refine pow_le_pow_left₀ bot_le (lintegral_mono fun ζ => ?_) 2
          calc modWt (-β) k (-(2 * Real.pi) * ξ) * (‖κ (ξ - ζ)‖ₑ * ‖θ ζ‖ₑ)
              = (modWt (-β) k (-(2 * Real.pi) * ξ) * ‖κ (ξ - ζ)‖ₑ *
                  modWt α k (-(2 * Real.pi) * ζ)) * g ζ := by
                rw [hgdef]
                calc modWt (-β) k (-(2 * Real.pi) * ξ) * (‖κ (ξ - ζ)‖ₑ * ‖θ ζ‖ₑ)
                    = modWt (-β) k (-(2 * Real.pi) * ξ) * ‖κ (ξ - ζ)‖ₑ *
                      (modWt (-α) k (-(2 * Real.pi) * ζ) * modWt α k (-(2 * Real.pi) * ζ)) *
                      ‖θ ζ‖ₑ := by rw [modWt_neg_mul]; ring
                  _ = _ := by ring
            _ ≤ (ENNReal.ofReal (δ ^ (-α)) * m ξ * R (ξ - ζ)) * g ζ :=
                mul_le_mul' (modWt_kernel_le (β := β) hα hδ R1 κ hκ k ξ ζ) le_rfl
            _ = _ := by ring
      _ = ENNReal.ofReal (δ ^ (-α)) ^ 2 * (m ξ ^ 2 * (∫⁻ ζ, R (ξ - ζ) * g ζ) ^ 2) := by
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            ENNReal.ofReal_ne_top)]
          ring
  have hB : ∀ y, ∫⁻ x, m x ^ 2 * R (x - y) ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
      ((A0 * ENNReal.ofReal (|(-(2 * Real.pi))⁻¹| * (2 / (1 - 2 * β))) + ∫⁻ u, R1 u) *
        ENNReal.ofReal (δ ^ (2 * β))) := fun y =>
    weight_kernel_integral_le hα hαβ hβ0 hβ hδ R1 hR1 A0 hA0 hRA lam y
  have hRint : ∫⁻ r, R r = ∫⁻ u, R1 u := by
    rw [hRdef, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_comp_mul_left_real R1 hδ.ne', ← mul_assoc, ← ENNReal.ofReal_mul hδ.le,
      abs_of_pos (inv_pos.2 hδ), mul_inv_cancel₀ hδ.ne', ENNReal.ofReal_one, one_mul]
  have hg2 : ∫⁻ ζ, g ζ ^ 2 = ∫⁻ ζ, modWt (-(2 * α)) k (-(2 * Real.pi) * ζ) * ‖θ ζ‖ₑ ^ 2 := by
    refine lintegral_congr fun ζ => ?_
    rw [hgdef, mul_pow, modWt_sq, mul_neg]
  have hδpow : ENNReal.ofReal (δ ^ (-α)) ^ 2 * ENNReal.ofReal (δ ^ (2 * β)) =
      ENNReal.ofReal (δ ^ (2 * β - 2 * α)) := by
    rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hδ.le _),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg hδ.le _) 2), rpow_sq_eq hδ.le,
      ← Real.rpow_add hδ]
    congr 2
    ring
  have hA := lintegral_sq_conv_le m R g hmm hRm hgm _ hB
  calc ∫⁻ ξ, modWt (-(2 * β)) k (-(2 * Real.pi) * ξ) * (∫⁻ ζ, ‖κ (ξ - ζ)‖ₑ * ‖θ ζ‖ₑ) ^ 2
      ≤ ∫⁻ ξ, ENNReal.ofReal (δ ^ (-α)) ^ 2 * (m ξ ^ 2 * (∫⁻ ζ, R (ξ - ζ) * g ζ) ^ 2) :=
        lintegral_mono hx
    _ = ENNReal.ofReal (δ ^ (-α)) ^ 2 * ∫⁻ ξ, m ξ ^ 2 * (∫⁻ ζ, R (ξ - ζ) * g ζ) ^ 2 :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal (δ ^ (-α)) ^ 2 * ((∫⁻ r, R r) * (ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
        ((A0 * ENNReal.ofReal (|(-(2 * Real.pi))⁻¹| * (2 / (1 - 2 * β))) + ∫⁻ u, R1 u) *
          ENNReal.ofReal (δ ^ (2 * β)))) * ∫⁻ ζ, g ζ ^ 2) := by gcongr
    _ = _ := by
        rw [hRint, hg2, ← hδpow]
        ring

end LiebLiniger.FixedPeriod.ALLS.PdeB
