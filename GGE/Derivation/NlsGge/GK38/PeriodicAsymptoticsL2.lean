import NlsGge.GK38.PeriodicAsymptoticsSine

/-! # S3: finite-central and quarter-disc localization of a square sum

Finite-window estimates establish summability before the real tsum bound. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

/-- Localized sine square summability controls the full displacement square sum. -/
theorem localized_sine_l2_38 (υ : ℤ → ℂ) (N : ℕ) (b C : ℝ)
    (_hb : 0 ≤ b) (_hC : 0 ≤ C)
    (hshift : ∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ b)
    (hfar : ∀ n : ℤ, (N : ℤ) < |n| →
      ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ Real.pi / 4)
    (hsin : Summable (fun n : ℤ => ‖Complex.sin (υ n)‖ ^ 2))
    (hbound : (∑' n : ℤ, ‖Complex.sin (υ n)‖ ^ 2) ≤ C) :
    Summable (fun n : ℤ => ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      (∑' n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤
        ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) * b ^ 2 +
          (Real.pi / 2 + 1) ^ 2 * C := by
  classical
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let K : ℝ := Real.pi / 2 + 1
  have hp (n : ℤ) : ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 ≤
      (if n ∈ S then b ^ 2 else 0) + K ^ 2 * ‖Complex.sin (υ n)‖ ^ 2 := by
    by_cases hn : n ∈ S
    · rw [if_pos hn]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hshift n) 2).trans
        (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    · rw [if_neg hn, zero_add]
      have hnf : (N : ℤ) < |n| := by
        have hh : ¬ (-(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) := by simpa [S] using hn
        by_contra h
        exact hh (abs_le.mp (not_lt.mp h))
      have hs := norm_le_quarter_sine38 (υ n - (n : ℂ) * (Real.pi : ℂ)) (hfar n hnf)
      rw [norm_sin_sub_int_pi38] at hs
      have ht := pow_le_pow_left₀ (norm_nonneg _) hs 2
      simpa only [mul_pow] using ht
  have hfinite (T : Finset ℤ) :
      ∑ n ∈ T, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 ≤
        (S.card : ℝ) * b ^ 2 + K ^ 2 * C := by
    have hcentral : (∑ n ∈ T, if n ∈ S then b ^ 2 else 0) ≤ (S.card : ℝ) * b ^ 2 := by
      rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((T ∩ S).card : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : T ∩ S ⊆ S)
      exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    have hs : (∑ n ∈ T, ‖Complex.sin (υ n)‖ ^ 2) ≤ C :=
      (hsin.sum_le_tsum T (fun n _ => sq_nonneg _)).trans hbound
    calc _ ≤ ∑ n ∈ T, ((if n ∈ S then b ^ 2 else 0) + K ^ 2 * ‖Complex.sin (υ n)‖ ^ 2) :=
        Finset.sum_le_sum (fun n _ => hp n)
      _ = (∑ n ∈ T, if n ∈ S then b ^ 2 else 0) + K ^ 2 * (∑ n ∈ T, ‖Complex.sin (υ n)‖ ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ _ := add_le_add hcentral (mul_le_mul_of_nonneg_left hs (sq_nonneg _))
  have hs := summable_of_sum_le (fun n : ℤ => sq_nonneg ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩

end
end NlsGge.GK38
