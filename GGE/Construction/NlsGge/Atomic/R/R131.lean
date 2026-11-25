import Mathlib

namespace NlsGge.Atomic.R131

                                                                                                       
-- Witness: the piecewise-linear ramp chi r = max 0 (min 1 (2 - r)); it is continuous, equals 1 on (-inf, 1],
-- 0 on [2, inf), and so has the required values on chi(x/R) for the radius-R and radius-2R clauses.

theorem R131 :
  ∃ χ : ℝ → ℝ, Continuous χ ∧
    (∀ r : ℝ, 0 ≤ r → 0 ≤ χ r ∧ χ r ≤ 1) ∧
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 → χ r = 1) ∧
    (∀ r : ℝ, 2 ≤ r → χ r = 0) ∧
    (∀ R : ℝ, 0 < R → ∀ x : ℝ, 0 ≤ x → x ≤ R → χ (x / R) = 1) ∧
    (∀ R : ℝ, 0 < R → ∀ x : ℝ, 0 ≤ x → 2 * R ≤ x → χ (x / R) = 0) ∧
    (∀ x : ℝ, 0 ≤ x → Filter.Tendsto (fun R : ℝ => χ (x / R)) Filter.atTop (nhds 1)) := by
  set χ : ℝ → ℝ := fun r => max 0 (min 1 (2 - r)) with hχ
  have one_of_le : ∀ r : ℝ, r ≤ 1 → χ r = 1 := by
    intro r hr
    simp only [hχ]
    rw [min_eq_left (show (1 : ℝ) ≤ 2 - r by linarith), max_eq_right zero_le_one]
  have zero_of_ge : ∀ r : ℝ, 2 ≤ r → χ r = 0 := by
    intro r hr
    simp only [hχ]
    rw [min_eq_right (show 2 - r ≤ (1 : ℝ) by linarith), max_eq_left (show 2 - r ≤ (0 : ℝ) by linarith)]
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hχ]
    fun_prop
  · intro r _
    constructor
    · exact le_max_left _ _
    · exact max_le zero_le_one (min_le_left _ _)
  · intro r _ hr1
    exact one_of_le r hr1
  · intro r hr
    exact zero_of_ge r hr
  · intro R hR x hx hxR
    apply one_of_le
    exact (div_le_one hR).mpr hxR
  · intro R hR x hx h2R
    apply zero_of_ge
    rw [le_div_iff₀ hR]
    linarith
  · intro x hx
    have hev : ∀ᶠ R in Filter.atTop, χ (x / R) = 1 := by
      filter_upwards [Filter.eventually_ge_atTop (max x 1)] with R hR
      have hR0 : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hR)
      apply one_of_le
      rw [div_le_one hR0]
      exact le_trans (le_max_left _ _) hR
    exact tendsto_const_nhds.congr' (by filter_upwards [hev] with R hR; exact hR.symm)

end NlsGge.Atomic.R131
