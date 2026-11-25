import Mathlib
import NlsGge.Atomic.M.M054
import NlsGge.Atomic.M.M055
import NlsGge.Atomic.M.M056

                                                                                                  
                                                                                
                                                                                           
                                                                                 
                                                                    

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M.M022
noncomputable section

theorem indexWeight_add_le (a b : ℤ) :
    NlsGge.Atomic.M.M054.indexWeight (a + b) ≤
      NlsGge.Atomic.M.M054.indexWeight a * NlsGge.Atomic.M.M054.indexWeight b := by
  unfold NlsGge.Atomic.M.M054.indexWeight
  have h1 : |((a + b : ℤ) : ℝ)| ≤ |(a : ℝ)| + |(b : ℝ)| := by
    push_cast
    exact abs_add_le _ _
  have h2 : 0 ≤ |(a : ℝ)| * |(b : ℝ)| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

theorem indexWeight_neg (j : ℤ) :
    NlsGge.Atomic.M.M054.indexWeight (-j) = NlsGge.Atomic.M.M054.indexWeight j := by
  unfold NlsGge.Atomic.M.M054.indexWeight
  push_cast
  rw [abs_neg]

theorem summable_inv_sq_shift (s : ℤ) :
    Summable (fun m : ℤ => 1 / ((m + s : ℤ) : ℝ) ^ 2) := by
  have h0 : Summable (fun d : ℤ => 1 / (d : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  exact h0.comp_injective (i := fun m : ℤ => m + s) (add_left_injective s)

theorem summable_inv_sq_sub (s : ℤ) :
    Summable (fun l : ℤ => 1 / ((l - s : ℤ) : ℝ) ^ 2) := by
  simpa only [sub_eq_add_neg] using summable_inv_sq_shift (-s)

/-- rho(m+s) <= rho(m-l) * rho(l+s) with rho j = 1 + |j|. -/
theorem rho_shift_le (m l s : ℤ) :
    1 + |((m + s : ℤ) : ℝ)| ≤
      (1 + |((m - l : ℤ) : ℝ)|) * (1 + |((l + s : ℤ) : ℝ)|) := by
  have h1 : |((m + s : ℤ) : ℝ)| ≤ |((m - l : ℤ) : ℝ)| + |((l + s : ℤ) : ℝ)| := by
    have e : ((m + s : ℤ) : ℝ) = ((m - l : ℤ) : ℝ) + ((l + s : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]
    exact abs_add_le _ _
  have h2 : 0 ≤ |((m - l : ℤ) : ℝ)| * |((l + s : ℤ) : ℝ)| :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

/-- Termwise comparison with the M-055 summand (n' = -s, l' = -l), for m + s ≠ 0. -/
theorem m055_term_le (s l m : ℤ) (hm : m + s ≠ 0) :
    (1 + |((m - -s : ℤ) : ℝ)|) ^ 2 /
        ((1 + |((m + -l : ℤ) : ℝ)|) ^ 2 * |((-s - m : ℤ) : ℝ)| ^ 2) ≤
      (1 + |((l + s : ℤ) : ℝ)|) ^ 2 * (1 / ((m + s : ℤ) : ℝ) ^ 2) := by
  have c1 : ((m - -s : ℤ) : ℝ) = ((m + s : ℤ) : ℝ) := by push_cast; ring
  have c2 : ((m + -l : ℤ) : ℝ) = ((m - l : ℤ) : ℝ) := by push_cast; ring
  have c3 : |((-s - m : ℤ) : ℝ)| = |((m + s : ℤ) : ℝ)| := by
    rw [← abs_neg]
    congr 1
    push_cast
    ring
  rw [c1, c2, c3]
  have hne : ((m + s : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hpos : 0 < |((m + s : ℤ) : ℝ)| := abs_pos.mpr hne
  have hB0 : |((m + s : ℤ) : ℝ)| ^ 2 ≠ 0 := pow_ne_zero 2 hpos.ne'
  have hA0 : (1 + |((m - l : ℤ) : ℝ)|) ^ 2 ≠ 0 := by positivity
  have hX : (1 + |((m + s : ℤ) : ℝ)|) ^ 2 ≤
      (1 + |((m - l : ℤ) : ℝ)|) ^ 2 * (1 + |((l + s : ℤ) : ℝ)|) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (rho_shift_le m l s) 2
  calc (1 + |((m + s : ℤ) : ℝ)|) ^ 2 /
        ((1 + |((m - l : ℤ) : ℝ)|) ^ 2 * |((m + s : ℤ) : ℝ)| ^ 2)
      ≤ ((1 + |((m - l : ℤ) : ℝ)|) ^ 2 * (1 + |((l + s : ℤ) : ℝ)|) ^ 2) /
          ((1 + |((m - l : ℤ) : ℝ)|) ^ 2 * |((m + s : ℤ) : ℝ)| ^ 2) :=
        div_le_div_of_nonneg_right hX (by positivity)
    _ = (1 + |((l + s : ℤ) : ℝ)|) ^ 2 * (1 / |((m + s : ℤ) : ℝ)| ^ 2) := by
        field_simp
    _ = (1 + |((l + s : ℤ) : ℝ)|) ^ 2 * (1 / ((m + s : ℤ) : ℝ) ^ 2) := by
        rw [sq_abs]

/-- Outer column sum. Hypothesis: the kernel bound with zero at m + s = 0. -/
theorem outer_col (s : ℤ) (α : ℤ → ℂ)
    (hα : ∀ m : ℤ, ‖α m‖ ≤ if m + s = 0 then 0 else 1 / |((m + s : ℤ) : ℝ)|) (l : ℤ) :
    Summable (fun m : ℤ =>
      ‖α m‖ ^ 2 * ((1 + |((m + s : ℤ) : ℝ)|) ^ 2 / (1 + |((m - l : ℤ) : ℝ)|) ^ 2)) ∧
    ∑' m : ℤ,
      ‖α m‖ ^ 2 * ((1 + |((m + s : ℤ) : ℝ)|) ^ 2 / (1 + |((m - l : ℤ) : ℝ)|) ^ 2) ≤
      32 / 5 := by
  have hM := NlsGge.Atomic.M.M055.first_two_resolvent_kernel_sum (-s) (-l)
  have hsumm : Summable (fun m : ℤ =>
      if m = -s then (0 : ℝ) else
        (1 + |((m - -s : ℤ) : ℝ)|) ^ 2 /
          ((1 + |((m + -l : ℤ) : ℝ)|) ^ 2 * |((-s - m : ℤ) : ℝ)| ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
      ((summable_inv_sq_shift s).mul_left ((1 + |((l + s : ℤ) : ℝ)|) ^ 2))
    · split_ifs <;> positivity
    · by_cases hm : m = -s
      · rw [if_pos hm]
        positivity
      · rw [if_neg hm]
        exact m055_term_le s l m (fun h => hm (by omega))
  have hgle : ∀ m : ℤ,
      ‖α m‖ ^ 2 * ((1 + |((m + s : ℤ) : ℝ)|) ^ 2 / (1 + |((m - l : ℤ) : ℝ)|) ^ 2) ≤
      (if m = -s then (0 : ℝ) else
        (1 + |((m - -s : ℤ) : ℝ)|) ^ 2 /
          ((1 + |((m + -l : ℤ) : ℝ)|) ^ 2 * |((-s - m : ℤ) : ℝ)| ^ 2)) := by
    intro m
    by_cases hm : m = -s
    · have hms : m + s = 0 := by omega
      have h0 : ‖α m‖ ≤ 0 := by simpa [hms] using hα m
      have hz : ‖α m‖ = 0 := le_antisymm h0 (norm_nonneg _)
      rw [if_pos hm, hz]
      simp
    · rw [if_neg hm]
      have hms : m + s ≠ 0 := fun h => hm (by omega)
      have hpos : 0 < |((m + s : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hms)
      have ha : ‖α m‖ ≤ 1 / |((m + s : ℤ) : ℝ)| := by simpa [hms] using hα m
      have hsq : ‖α m‖ ^ 2 ≤ 1 / |((m + s : ℤ) : ℝ)| ^ 2 := by
        calc ‖α m‖ ^ 2 ≤ (1 / |((m + s : ℤ) : ℝ)|) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) ha 2
          _ = 1 / |((m + s : ℤ) : ℝ)| ^ 2 := by rw [div_pow, one_pow]
      have c1 : ((m - -s : ℤ) : ℝ) = ((m + s : ℤ) : ℝ) := by push_cast; ring
      have c2 : ((m + -l : ℤ) : ℝ) = ((m - l : ℤ) : ℝ) := by push_cast; ring
      have c3 : |((-s - m : ℤ) : ℝ)| = |((m + s : ℤ) : ℝ)| := by
        rw [← abs_neg]
        congr 1
        push_cast
        ring
      rw [c1, c2, c3]
      have hA : 0 ≤ (1 + |((m - l : ℤ) : ℝ)|) ^ 2 := by positivity
      calc ‖α m‖ ^ 2 * ((1 + |((m + s : ℤ) : ℝ)|) ^ 2 / (1 + |((m - l : ℤ) : ℝ)|) ^ 2)
          ≤ (1 / |((m + s : ℤ) : ℝ)| ^ 2) *
              ((1 + |((m + s : ℤ) : ℝ)|) ^ 2 / (1 + |((m - l : ℤ) : ℝ)|) ^ 2) :=
            mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = (1 + |((m + s : ℤ) : ℝ)|) ^ 2 /
              ((1 + |((m - l : ℤ) : ℝ)|) ^ 2 * |((m + s : ℤ) : ℝ)| ^ 2) := by
            field_simp
  have hsumm2 : Summable (fun m : ℤ =>
      ‖α m‖ ^ 2 * ((1 + |((m + s : ℤ) : ℝ)|) ^ 2 / (1 + |((m - l : ℤ) : ℝ)|) ^ 2)) :=
    Summable.of_nonneg_of_le (fun m => by positivity) hgle hsumm
  refine ⟨hsumm2, ?_⟩
  exact (Summable.tsum_le_tsum hgle hsumm2 hsumm).trans hM

/-- Termwise comparison of the M-056 row summand, for l ≠ s. -/
theorem m056_term_le (s l : ℤ) (hl : l ≠ s) :
    1 / ((1 + |((l + s : ℤ) : ℝ)|) ^ 2 * |((s - l : ℤ) : ℝ)| ^ 2) ≤
      1 / |((s - l : ℤ) : ℝ)| ^ 2 := by
  have hne : ((s - l : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (fun h => hl (by omega))
  have hpos : 0 < |((s - l : ℤ) : ℝ)| := abs_pos.mpr hne
  have hr : 1 ≤ (1 + |((l + s : ℤ) : ℝ)|) ^ 2 := by
    have : 0 ≤ |((l + s : ℤ) : ℝ)| := abs_nonneg _
    nlinarith
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [sq_nonneg |((s - l : ℤ) : ℝ)|]

/-- Row sum (M-056 with n' = s). -/
theorem inner_row (s : ℤ) (β : ℤ → ℂ)
    (hβ : ∀ l : ℤ, ‖β l‖ ≤ if l - s = 0 then 0 else 1 / |((l - s : ℤ) : ℝ)|) :
    Summable (fun l : ℤ => ‖β l‖ ^ 2 / (1 + |((l + s : ℤ) : ℝ)|) ^ 2) ∧
    ∑' l : ℤ, ‖β l‖ ^ 2 / (1 + |((l + s : ℤ) : ℝ)|) ^ 2 ≤
      (5 / 2 : ℝ) / (1 + |(s : ℝ)|) ^ 2 := by
  have hM := NlsGge.Atomic.M.M056.second_two_resolvent_kernel_sum s
  have hsq : ∀ l : ℤ, ‖β l‖ ^ 2 ≤ 1 / ((l - s : ℤ) : ℝ) ^ 2 := by
    intro l
    by_cases hl : l = s
    · have hz' : l - s = 0 := by omega
      have h0 : ‖β l‖ ≤ 0 := by
        have := hβ l
        rw [if_pos hz'] at this
        exact this
      have hz : ‖β l‖ = 0 := le_antisymm h0 (norm_nonneg _)
      rw [hz]
      have : ((l - s : ℤ) : ℝ) = 0 := Int.cast_eq_zero.mpr (by omega)
      rw [this]
      simp
    · have hb : ‖β l‖ ≤ 1 / |((l - s : ℤ) : ℝ)| := by
        have hnz : ¬ (l - s = 0) := fun h => hl (by omega)
        have := hβ l
        rw [if_neg hnz] at this
        exact this
      calc ‖β l‖ ^ 2 ≤ (1 / |((l - s : ℤ) : ℝ)|) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ = 1 / ((l - s : ℤ) : ℝ) ^ 2 := by rw [div_pow, sq_abs]; ring
  have hmaj : Summable (fun l : ℤ => 1 / ((l - s : ℤ) : ℝ) ^ 2) := summable_inv_sq_sub s
  have hmaj_row : ∀ l : ℤ, ‖β l‖ ^ 2 / (1 + |((l + s : ℤ) : ℝ)|) ^ 2 ≤ 1 / ((l - s : ℤ) : ℝ) ^ 2 := by
    intro l
    have hr : 1 ≤ (1 + |((l + s : ℤ) : ℝ)|) ^ 2 := by
      have : 0 ≤ |((l + s : ℤ) : ℝ)| := abs_nonneg _
      nlinarith
    calc ‖β l‖ ^ 2 / (1 + |((l + s : ℤ) : ℝ)|) ^ 2 ≤ ‖β l‖ ^ 2 :=
          div_le_self (by positivity) hr
      _ ≤ 1 / ((l - s : ℤ) : ℝ) ^ 2 := hsq l
  have hsumm : Summable (fun l : ℤ =>
      if l = s then (0 : ℝ) else 1 / ((1 + |((l + s : ℤ) : ℝ)|) ^ 2 * |((s - l : ℤ) : ℝ)| ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) hmaj
    · split_ifs <;> positivity
    · by_cases hl : l = s
      · rw [if_pos hl]
        have : ((l - s : ℤ) : ℝ) = 0 := Int.cast_eq_zero.mpr (by omega)
        rw [this]
        simp
      · rw [if_neg hl, show ((l - s : ℤ) : ℝ) ^ 2 = |((s - l : ℤ) : ℝ)| ^ 2 by
          rw [sq_abs]; push_cast; ring]
        exact m056_term_le s l hl
  have hgle : ∀ l : ℤ, ‖β l‖ ^ 2 / (1 + |((l + s : ℤ) : ℝ)|) ^ 2 ≤
      (if l = s then (0 : ℝ) else 1 / ((1 + |((l + s : ℤ) : ℝ)|) ^ 2 * |((s - l : ℤ) : ℝ)| ^ 2)) := by
    intro l
    by_cases hl : l = s
    · rw [if_pos hl]
      have hz' : l - s = 0 := by omega
      have h0 : ‖β l‖ ≤ 0 := by
        have := hβ l
        rw [if_pos hz'] at this
        exact this
      have hz : ‖β l‖ = 0 := le_antisymm h0 (norm_nonneg _)
      rw [hz]
      simp
    · rw [if_neg hl]
      have hb : ‖β l‖ ≤ 1 / |((l - s : ℤ) : ℝ)| := by
        have hnz : ¬ (l - s = 0) := fun h => hl (by omega)
        have := hβ l
        rw [if_neg hnz] at this
        exact this
      have hnum : ‖β l‖ ^ 2 ≤ 1 / |((s - l : ℤ) : ℝ)| ^ 2 := by
        have e : |((l - s : ℤ) : ℝ)| = |((s - l : ℤ) : ℝ)| := by
          rw [← abs_neg]; congr 1; push_cast; ring
        rw [← e]
        calc ‖β l‖ ^ 2 ≤ (1 / |((l - s : ℤ) : ℝ)|) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hb 2
          _ = 1 / |((l - s : ℤ) : ℝ)| ^ 2 := by rw [div_pow, one_pow]
      have hr : 1 ≤ (1 + |((l + s : ℤ) : ℝ)|) ^ 2 := by
        have : 0 ≤ |((l + s : ℤ) : ℝ)| := abs_nonneg _
        nlinarith
      have hd : 0 < |((s - l : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (fun h => hl (by omega)))
      calc ‖β l‖ ^ 2 / (1 + |((l + s : ℤ) : ℝ)|) ^ 2 ≤ (1 / |((s - l : ℤ) : ℝ)| ^ 2) / (1 + |((l + s : ℤ) : ℝ)|) ^ 2 :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = 1 / ((1 + |((l + s : ℤ) : ℝ)|) ^ 2 * |((s - l : ℤ) : ℝ)| ^ 2) := by
            field_simp
  have hsumm2 : Summable (fun l : ℤ => ‖β l‖ ^ 2 / (1 + |((l + s : ℤ) : ℝ)|) ^ 2) :=
    Summable.of_nonneg_of_le (fun l => by positivity) hgle hsumm
  refine ⟨hsumm2, ?_⟩
  exact (Summable.tsum_le_tsum hgle hsumm2 hsumm).trans hM

end
end NlsGge.ThirdConsultation.M.M022
