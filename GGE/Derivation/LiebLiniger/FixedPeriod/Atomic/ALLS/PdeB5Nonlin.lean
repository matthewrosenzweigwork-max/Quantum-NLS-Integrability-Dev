import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB5FreeL4

/-! # Track B, package 2: the cubic nonlinearity `L⁴ → L^{4/3}`

* pointwise: `|N(a) - N(b)| ≤ 3 (|a|² + |b|²) |a - b|` for `N(z) = 2|z|²z` (`cubicNL`);
* Hölder (`1/(4/3) = 1/2 + 1/4`): for any measure,
  `‖N∘a - N∘b‖_{L^{4/3}} ≤ 3 (‖a‖²_{L⁴} + ‖b‖²_{L⁴}) ‖a - b‖_{L⁴}` and `‖N∘a‖_{L^{4/3}} ≤ 3‖a‖³_{L⁴}`;
* `MemLp a 4 μ → MemLp (N∘a) (4/3) μ`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot
open scoped ENNReal

theorem continuous_cubicNL : Continuous cubicNL := by
  unfold cubicNL
  fun_prop

theorem cubicNL_zero : cubicNL 0 = 0 := by simp [cubicNL]

theorem norm_cubicNL_sub_le (a b : ℂ) :
    ‖cubicNL a - cubicNL b‖ ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2) * ‖a - b‖ := by
  have e : cubicNL a - cubicNL b =
      2 * (((‖a‖ ^ 2 : ℝ) : ℂ) * (a - b) + ((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) * b) := by
    unfold cubicNL; push_cast; ring
  have h1 : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
  have h2 : |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ ‖a - b‖ * (‖a‖ + ‖b‖) := by
    rw [show ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by ring, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖a‖ + ‖b‖)]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  rw [e, norm_mul, norm_two_complex]
  calc 2 * ‖((‖a‖ ^ 2 : ℝ) : ℂ) * (a - b) + ((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) * b‖
      ≤ 2 * (‖a‖ ^ 2 * ‖a - b‖ + (‖a - b‖ * (‖a‖ + ‖b‖)) * ‖b‖) := by
        gcongr
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2) * ‖a - b‖ := by
        nlinarith [mul_nonneg (norm_nonneg (a - b)) (sq_nonneg (‖a‖ - ‖b‖))]

/-- Hölder exponents `1/2 + 1/4 = 3/4`. -/
instance holderTriple_two_four : ENNReal.HolderTriple 2 4 (4 / 3) := by
  constructor
  rw [four_thirds_eq]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by simp
  rw [h2, h4, ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num),
    ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

section Holder

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem eLpNorm_norm_sq {a : α → ℂ} (ha : AEStronglyMeasurable a μ) :
    eLpNorm (fun p => ‖a p‖ ^ 2) 2 μ = eLpNorm a 4 μ ^ 2 := by
  have h := eLpNorm_norm_rpow (p := 2) (μ := μ) a (q := 2) ha (by norm_num)
  have e1 : (fun p => ‖a p‖ ^ (2 : ℝ)) = fun p => ‖a p‖ ^ 2 := funext fun p => Real.rpow_two _
  have e2 : (2 : ℝ≥0∞) * ENNReal.ofReal 2 = 4 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [e1, e2, ENNReal.rpow_two] at h
  exact h

/-- **Lipschitz estimate of the cubic `L⁴ → L^{4/3}`** (any measure). -/
theorem eLpNorm_cubic_sub_le {a b : α → ℂ} (ha : AEStronglyMeasurable a μ)
    (hb : AEStronglyMeasurable b μ) :
    eLpNorm (fun p => cubicNL (a p) - cubicNL (b p)) (4 / 3) μ ≤
      3 * (eLpNorm a 4 μ ^ 2 + eLpNorm b 4 μ ^ 2) * eLpNorm (a - b) 4 μ := by
  set g : α → ℝ := fun p => ‖a p‖ ^ 2 + ‖b p‖ ^ 2 with hg
  have hgm : AEStronglyMeasurable g μ := (ha.norm.pow 2).add (hb.norm.pow 2)
  have hφm : AEStronglyMeasurable ((3 : ℝ) • g) μ := hgm.const_smul 3
  calc eLpNorm (fun p => cubicNL (a p) - cubicNL (b p)) (4 / 3) μ
      ≤ eLpNorm (((3 : ℝ) • g) • (a - b)) (4 / 3) μ := by
        refine eLpNorm_mono_ae ((continuous_cubicNL.comp_aestronglyMeasurable ha).sub
          (continuous_cubicNL.comp_aestronglyMeasurable hb)) (Eventually.of_forall fun p => ?_)
        show ‖cubicNL (a p) - cubicNL (b p)‖ ≤
          ‖((3 : ℝ) * (‖a p‖ ^ 2 + ‖b p‖ ^ 2)) • (a p - b p)‖
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        exact norm_cubicNL_sub_le _ _
    _ ≤ eLpNorm ((3 : ℝ) • g) 2 μ * eLpNorm (a - b) 4 μ :=
        eLpNorm_smul_le_mul_eLpNorm hφm (ha.sub hb)
    _ ≤ 3 * (eLpNorm a 4 μ ^ 2 + eLpNorm b 4 μ ^ 2) * eLpNorm (a - b) 4 μ := by
        gcongr
        rw [eLpNorm_const_smul]
        have h3 : ‖(3 : ℝ)‖ₑ = 3 := by
          rw [← ofReal_norm, Real.norm_of_nonneg (by norm_num)]; simp
        rw [h3]
        gcongr
        refine (eLpNorm_add_le (by norm_num)).trans (le_of_eq ?_)
        rw [eLpNorm_norm_sq ha, eLpNorm_norm_sq hb]

theorem eLpNorm_cubic_le {a : α → ℂ} (ha : AEStronglyMeasurable a μ) :
    eLpNorm (fun p => cubicNL (a p)) (4 / 3) μ ≤ 3 * eLpNorm a 4 μ ^ 3 := by
  have h := eLpNorm_cubic_sub_le ha (aestronglyMeasurable_zero (μ := μ) (β := ℂ))
  simp only [Pi.zero_apply, cubicNL_zero, sub_zero, eLpNorm_zero] at h
  refine h.trans (le_of_eq ?_)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  ring

theorem memLp_cubic {a : α → ℂ} (ha : MemLp a 4 μ) :
    MemLp (fun p => cubicNL (a p)) (4 / 3) μ := by
  have h2 : eLpNorm (fun p => cubicNL (a p)) (4 / 3) μ < ⊤ :=
    (eLpNorm_cubic_le ha.aestronglyMeasurable).trans_lt
      (ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top ha.eLpNorm_lt_top))
  exact h2

end Holder

end LiebLiniger.FixedPeriod.ALLS.PdeB
