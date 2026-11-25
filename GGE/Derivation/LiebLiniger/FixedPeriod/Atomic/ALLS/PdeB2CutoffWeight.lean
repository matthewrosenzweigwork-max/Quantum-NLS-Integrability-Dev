import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB2CutoffCore

/-! # Track B, step B2: the uniform weight integral of the cutoff gain

With `m_δ(p) = ⟨p⟩^{-β} (1 + δ⟨p⟩)^α`, `0 ≤ α ≤ β`, `0 < β < 1/2`, `0 < δ ≤ 1`, and a kernel
`R_δ(r) = δ R₁(δ r)` with `R₁ ≤ A₀`:
`∫ m_δ(-2πξ + λ)² R_δ(ξ - ζ) dξ ≤ C (A₀ + ∫R₁) δ^{2β}` uniformly in `λ, ζ, δ`.
Pointwise: `m_δ² ≤ 2^{2α} (low(p) + δ^{2β})` with `low(p) = ⟨p⟩^{-2β} 1_{δ⟨p⟩ ≤ 1}`;
`∫ low ≤ 2 (1/δ)^{1-2β}/(1-2β)` (`integral_Ioc_sym_brk_rpow_le`), which is where `2β < 1` enters.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Set
open scoped ENNReal

/-- The low-modulation part `⟨u⟩^{-2β} 1_{δ⟨u⟩ ≤ 1}`. -/
def lowPart (β δ u : ℝ) : ℝ := if δ * brk u ≤ 1 then brk u ^ (-(2 * β)) else 0

theorem lowPart_nonneg (β δ u : ℝ) : 0 ≤ lowPart β δ u := by
  unfold lowPart
  split_ifs
  · exact brk_rpow_nonneg _ _
  · exact le_refl 0

theorem rpow_sq_eq {x : ℝ} (hx : 0 ≤ x) (r : ℝ) : (x ^ r) ^ 2 = x ^ (2 * r) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- Pointwise bound `m_δ(u)² ≤ 2^{2α} (low(u) + δ^{2β})`. -/
theorem weight_sq_le {α β δ : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hδ : 0 < δ) (u : ℝ) :
    (brk u ^ (-β) * (1 + δ * brk u) ^ α) ^ 2 ≤
      (2 : ℝ) ^ (2 * α) * (lowPart β δ u + δ ^ (2 * β)) := by
  have hb0 : 0 < brk u := brk_pos u
  have h1d : 0 ≤ 1 + δ * brk u := add_nonneg zero_le_one (mul_nonneg hδ.le hb0.le)
  have hm0 : 0 ≤ brk u ^ (-β) * (1 + δ * brk u) ^ α :=
    mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg h1d _)
  have h2a : (0 : ℝ) ≤ 2 ^ α := Real.rpow_nonneg (by norm_num) _
  by_cases h : δ * brk u ≤ 1
  · have h1 : (1 + δ * brk u) ^ α ≤ 2 ^ α := Real.rpow_le_rpow h1d (by linarith) hα
    have hm : brk u ^ (-β) * (1 + δ * brk u) ^ α ≤ brk u ^ (-β) * 2 ^ α :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hb0.le _)
    have hlow : lowPart β δ u = brk u ^ (-(2 * β)) := by simp [lowPart, h]
    calc (brk u ^ (-β) * (1 + δ * brk u) ^ α) ^ 2 ≤ (brk u ^ (-β) * 2 ^ α) ^ 2 :=
          pow_le_pow_left₀ hm0 hm 2
      _ = (2 : ℝ) ^ (2 * α) * brk u ^ (-(2 * β)) := by
          rw [mul_pow, rpow_sq_eq hb0.le, rpow_sq_eq (by norm_num : (0 : ℝ) ≤ 2), mul_comm,
            show (2 : ℝ) * -β = -(2 * β) by ring]
      _ ≤ (2 : ℝ) ^ (2 * α) * (lowPart β δ u + δ ^ (2 * β)) := by
          rw [hlow]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg hδ.le _))
            (Real.rpow_nonneg (by norm_num) _)
  · rw [not_le] at h
    have h1 : 1 + δ * brk u ≤ 2 * (δ * brk u) := by linarith
    have h2 : (1 + δ * brk u) ^ α ≤ (2 * (δ * brk u)) ^ α := Real.rpow_le_rpow h1d h1 hα
    rw [Real.mul_rpow (by norm_num) (mul_nonneg hδ.le hb0.le), Real.mul_rpow hδ.le hb0.le] at h2
    have hbd : δ⁻¹ ≤ brk u := by
      rw [inv_le_iff_one_le_mul₀' hδ]
      exact h.le
    have h3 : brk u ^ (α - β) ≤ δ ^ (β - α) := by
      calc brk u ^ (α - β) ≤ (δ⁻¹) ^ (α - β) :=
            Real.rpow_le_rpow_of_nonpos (inv_pos.2 hδ) hbd (by linarith)
        _ = δ ^ (β - α) := by rw [Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le, neg_sub]
    have hm : brk u ^ (-β) * (1 + δ * brk u) ^ α ≤ 2 ^ α * δ ^ β := by
      calc brk u ^ (-β) * (1 + δ * brk u) ^ α
          ≤ brk u ^ (-β) * (2 ^ α * (δ ^ α * brk u ^ α)) :=
            mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hb0.le _)
        _ = 2 ^ α * δ ^ α * brk u ^ (α - β) := by
            rw [Real.rpow_sub hb0, Real.rpow_neg hb0.le]
            ring
        _ ≤ 2 ^ α * δ ^ α * δ ^ (β - α) :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg h2a (Real.rpow_nonneg hδ.le _))
        _ = 2 ^ α * δ ^ β := by
            rw [mul_assoc, ← Real.rpow_add hδ]
            congr 2
            ring
    calc (brk u ^ (-β) * (1 + δ * brk u) ^ α) ^ 2 ≤ (2 ^ α * δ ^ β) ^ 2 :=
          pow_le_pow_left₀ hm0 hm 2
      _ = (2 : ℝ) ^ (2 * α) * δ ^ (2 * β) := by
          rw [mul_pow, rpow_sq_eq (by norm_num : (0 : ℝ) ≤ 2), rpow_sq_eq hδ.le]
      _ ≤ (2 : ℝ) ^ (2 * α) * (lowPart β δ u + δ ^ (2 * β)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (lowPart_nonneg β δ u))
            (Real.rpow_nonneg (by norm_num) _)

/-- `|u| < ⟨u⟩`. -/
theorem abs_lt_brk (u : ℝ) : |u| < brk u := by
  have h := brk_sq u
  have h2 : |u| ^ 2 < brk u ^ 2 := by rw [h, sq_abs]; linarith
  exact lt_of_pow_lt_pow_left₀ 2 (brk_pos u).le h2

/-- `∫ low ≤ 2 (1/δ)^{1-2β}/(1-2β)` for `0 < β < 1/2`, `0 < δ`. -/
theorem lintegral_lowPart_le {β δ : ℝ} (hβ0 : 0 < β) (hβ : β < 1 / 2) (hδ : 0 < δ) :
    ∫⁻ u, ENNReal.ofReal (lowPart β δ u) ≤
      ENNReal.ofReal (2 * ((δ⁻¹) ^ (1 - 2 * β) / (1 - 2 * β))) := by
  have hpt : ∀ u, ENNReal.ofReal (lowPart β δ u) ≤
      (Ioc (-δ⁻¹) δ⁻¹).indicator (fun u => ENNReal.ofReal (brk u ^ (-(2 * β)))) u := by
    intro u
    unfold lowPart
    split_ifs with h
    · have hu : u ∈ Ioc (-δ⁻¹) δ⁻¹ := by
        have h1 : brk u ≤ δ⁻¹ := by
          have h0 : brk u ≤ 1 / δ := (le_div_iff₀ hδ).2 (by linarith [mul_comm δ (brk u)])
          rwa [one_div] at h0
        have h2 := abs_lt_brk u
        rw [mem_Ioc]
        constructor
        · linarith [neg_abs_le u]
        · linarith [le_abs_self u]
      rw [indicator_of_mem hu]
    · simp
  calc ∫⁻ u, ENNReal.ofReal (lowPart β δ u)
      ≤ ∫⁻ u, (Ioc (-δ⁻¹) δ⁻¹).indicator (fun u => ENNReal.ofReal (brk u ^ (-(2 * β)))) u :=
        lintegral_mono hpt
    _ = ∫⁻ u in Ioc (-δ⁻¹) δ⁻¹, ENNReal.ofReal (brk u ^ (-(2 * β))) :=
        lintegral_indicator measurableSet_Ioc _
    _ = ENNReal.ofReal (∫ u in Ioc (-δ⁻¹) δ⁻¹, brk u ^ (-(2 * β))) :=
        (ofReal_integral_eq_lintegral_ofReal ((continuous_brk_rpow _).integrableOn_Ioc)
          (ae_of_all _ fun u => brk_rpow_nonneg _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
        (integral_Ioc_sym_brk_rpow_le (by linarith) (by linarith) (inv_pos.2 hδ).le)

/-- Affine change of variables `ξ ↦ -2πξ + λ` for lower integrals. -/
theorem lintegral_comp_affine (F : ℝ → ℝ≥0∞) (lam : ℝ) :
    ∫⁻ ξ, F (-(2 * Real.pi) * ξ + lam) =
      ENNReal.ofReal |(-(2 * Real.pi))⁻¹| * ∫⁻ u, F u := by
  have hc : -(2 * Real.pi) ≠ 0 := by have := Real.pi_pos; linarith
  rw [lintegral_comp_mul_left_real (fun v => F (v + lam)) hc]
  congr 1
  exact lintegral_add_right_eq_self F lam

/-- **Uniform weight integral of the cutoff gain** (`0 ≤ α ≤ β`, `0 < β < 1/2`, `0 < δ`):
`∫ m_δ(-2πξ+λ)² · δR₁(δ(ξ-ζ)) dξ ≤ 2^{2α} (A₀ K₁ + ∫R₁) δ^{2β}`, `K₁ = (2π)⁻¹ · 2/(1-2β)`. -/
theorem weight_kernel_integral_le {α β δ : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ0 : 0 < β)
    (hβ : β < 1 / 2) (hδ : 0 < δ) (R1 : ℝ → ℝ≥0∞) (hR1 : Measurable R1) (A0 : ℝ≥0∞)
    (hA0 : A0 ≠ ⊤) (hRA : ∀ u, R1 u ≤ A0) (lam ζ : ℝ) :
    ∫⁻ ξ, ENNReal.ofReal (brk (-(2 * Real.pi) * ξ + lam) ^ (-β) *
        (1 + δ * brk (-(2 * Real.pi) * ξ + lam)) ^ α) ^ 2 *
        (ENNReal.ofReal δ * R1 (δ * (ξ - ζ))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
        ((A0 * ENNReal.ofReal (|(-(2 * Real.pi))⁻¹| * (2 / (1 - 2 * β))) + ∫⁻ u, R1 u) *
          ENNReal.ofReal (δ ^ (2 * β))) := by
  set c : ℝ := -(2 * Real.pi) with hcdef
  set L : ℝ := δ⁻¹ ^ (1 - 2 * β) with hL
  have h12 : 0 < 1 - 2 * β := by linarith
  have hL0 : 0 ≤ L := Real.rpow_nonneg (inv_nonneg.2 hδ.le) _
  have hK : Measurable fun ξ : ℝ => ENNReal.ofReal δ * R1 (δ * (ξ - ζ)) :=
    measurable_const.mul (hR1.comp (measurable_const.mul (measurable_id.sub measurable_const)))
  have h2a : (0 : ℝ) ≤ 2 ^ (2 * α) := Real.rpow_nonneg (by norm_num) _
  have hδb : (0 : ℝ) ≤ δ ^ (2 * β) := Real.rpow_nonneg hδ.le _
  -- pointwise split
  have hpt : ∀ ξ, ENNReal.ofReal (brk (c * ξ + lam) ^ (-β) * (1 + δ * brk (c * ξ + lam)) ^ α) ^ 2 *
      (ENNReal.ofReal δ * R1 (δ * (ξ - ζ))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
        (ENNReal.ofReal (lowPart β δ (c * ξ + lam)) * (ENNReal.ofReal δ * A0) +
          ENNReal.ofReal (δ ^ (2 * β)) * (ENNReal.ofReal δ * R1 (δ * (ξ - ζ)))) := by
    intro ξ
    have hm0 : 0 ≤ brk (c * ξ + lam) ^ (-β) * (1 + δ * brk (c * ξ + lam)) ^ α :=
      mul_nonneg (brk_rpow_nonneg _ _)
        (Real.rpow_nonneg (add_nonneg zero_le_one (mul_nonneg hδ.le (brk_pos _).le)) _)
    rw [← ENNReal.ofReal_pow hm0]
    calc ENNReal.ofReal ((brk (c * ξ + lam) ^ (-β) * (1 + δ * brk (c * ξ + lam)) ^ α) ^ 2) *
          (ENNReal.ofReal δ * R1 (δ * (ξ - ζ)))
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * α) * (lowPart β δ (c * ξ + lam) + δ ^ (2 * β))) *
          (ENNReal.ofReal δ * R1 (δ * (ξ - ζ))) := by
          gcongr
          exact weight_sq_le hα hαβ hδ _
      _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
            (ENNReal.ofReal (lowPart β δ (c * ξ + lam)) * (ENNReal.ofReal δ * R1 (δ * (ξ - ζ))) +
              ENNReal.ofReal (δ ^ (2 * β)) * (ENNReal.ofReal δ * R1 (δ * (ξ - ζ)))) := by
          rw [ENNReal.ofReal_mul h2a, ENNReal.ofReal_add (lowPart_nonneg _ _ _) hδb]
          ring
      _ ≤ _ := by
          gcongr
          exact hRA _
  -- the kernel integral
  have hKint : ∫⁻ ξ, ENNReal.ofReal δ * R1 (δ * (ξ - ζ)) = ∫⁻ u, R1 u := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have h1 : ∫⁻ ξ, R1 (δ * (ξ - ζ)) = ∫⁻ x, R1 (δ * x) :=
      lintegral_sub_right_eq_self (fun x => R1 (δ * x)) ζ
    rw [h1, lintegral_comp_mul_left_real R1 hδ.ne', ← mul_assoc, ← ENNReal.ofReal_mul hδ.le,
      abs_of_pos (inv_pos.2 hδ), mul_inv_cancel₀ hδ.ne', ENNReal.ofReal_one, one_mul]
  -- the low part
  have hlow : ∫⁻ ξ, ENNReal.ofReal (lowPart β δ (c * ξ + lam)) ≤
      ENNReal.ofReal |c⁻¹| * ENNReal.ofReal (2 * (L / (1 - 2 * β))) := by
    rw [lintegral_comp_affine (fun u => ENNReal.ofReal (lowPart β δ u)) lam]
    gcongr
    exact lintegral_lowPart_le hβ0 hβ hδ
  have hδL : δ * L = δ ^ (2 * β) := by
    rw [hL, Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le]
    calc δ * δ ^ (-(1 - 2 * β)) = δ ^ (1 : ℝ) * δ ^ (-(1 - 2 * β)) := by rw [Real.rpow_one]
      _ = δ ^ (2 * β) := by
          rw [← Real.rpow_add hδ]
          congr 1
          ring
  have hreal : |c⁻¹| * (2 * (L / (1 - 2 * β))) * δ =
      |c⁻¹| * (2 / (1 - 2 * β)) * δ ^ (2 * β) := by
    rw [← hδL]
    ring
  have hb : 0 ≤ 2 * (L / (1 - 2 * β)) := mul_nonneg zero_le_two (div_nonneg hL0 h12.le)
  have hE : ENNReal.ofReal |c⁻¹| * ENNReal.ofReal (2 * (L / (1 - 2 * β))) *
      (ENNReal.ofReal δ * A0) =
      A0 * ENNReal.ofReal (|c⁻¹| * (2 / (1 - 2 * β))) * ENNReal.ofReal (δ ^ (2 * β)) := by
    rw [mul_assoc A0,
      ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (div_nonneg zero_le_two h12.le)), ← hreal,
      ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) hb), ENNReal.ofReal_mul (abs_nonneg _)]
    ring
  have hlowm : Measurable fun ξ : ℝ => ENNReal.ofReal (δ ^ (2 * β)) *
      (ENNReal.ofReal δ * R1 (δ * (ξ - ζ))) := measurable_const.mul hK
  calc ∫⁻ ξ, ENNReal.ofReal (brk (c * ξ + lam) ^ (-β) * (1 + δ * brk (c * ξ + lam)) ^ α) ^ 2 *
        (ENNReal.ofReal δ * R1 (δ * (ξ - ζ)))
      ≤ ∫⁻ ξ, ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
        (ENNReal.ofReal (lowPart β δ (c * ξ + lam)) * (ENNReal.ofReal δ * A0) +
          ENNReal.ofReal (δ ^ (2 * β)) * (ENNReal.ofReal δ * R1 (δ * (ξ - ζ)))) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
        ((∫⁻ ξ, ENNReal.ofReal (lowPart β δ (c * ξ + lam))) * (ENNReal.ofReal δ * A0) +
          ENNReal.ofReal (δ ^ (2 * β)) * ∫⁻ u, R1 u) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ hlowm,
          lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA0),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hKint]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
        (ENNReal.ofReal |c⁻¹| * ENNReal.ofReal (2 * (L / (1 - 2 * β))) * (ENNReal.ofReal δ * A0) +
          ENNReal.ofReal (δ ^ (2 * β)) * ∫⁻ u, R1 u) := by
        gcongr
    _ = _ := by
        rw [hE]
        ring

end LiebLiniger.FixedPeriod.ALLS.PdeB
