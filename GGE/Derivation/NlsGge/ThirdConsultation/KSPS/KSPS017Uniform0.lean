import Mathlib

/- KSPS017U0 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS017Uniform0.lean. Pro round-15 SUPPORT (never a packet), input h17U.
   Elementary finite-sum tools (Mathlib only): Cauchy–Schwarz for finitely many dominating sequences with explicit
   constant (sq_sum_le_card_mul_sum_sq), and Σ_F (1/|n|)² ≤ Σ' (1/|n|)². No hypothesis added. -/
set_option autoImplicit false
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS017U0
noncomputable section

/-- Cauchy–Schwarz for finitely many dominating sequences, with explicit constant. -/
theorem sum_sq_le_fin {ι : Type*} {m : ℕ} (F : Finset ι) (x : ι → ℝ) (t : Fin m → ι → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (h : ∀ n ∈ F, 0 ≤ x n ∧ x n ≤ K * ∑ j, t j n) (T : Fin m → ℝ)
    (hT : ∀ j, ∑ n ∈ F, t j n ^ 2 ≤ T j) :
    ∑ n ∈ F, x n ^ 2 ≤ K ^ 2 * ((m : ℝ) * ∑ j, T j) := by
  have hp : ∀ n ∈ F, x n ^ 2 ≤ K ^ 2 * ((m : ℝ) * ∑ j, t j n ^ 2) := by
    intro n hn
    obtain ⟨h0, hle⟩ := h n hn
    calc x n ^ 2 ≤ (K * ∑ j, t j n) ^ 2 := pow_le_pow_left₀ h0 hle 2
      _ = K ^ 2 * (∑ j, t j n) ^ 2 := by ring
      _ ≤ K ^ 2 * ((m : ℝ) * ∑ j, t j n ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m))) (f := fun j => t j n)
        simpa using this
  refine (Finset.sum_le_sum hp).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun j _ => hT j)) (Nat.cast_nonneg m)) (sq_nonneg K)

theorem inv_abs_sq_summable : Summable (fun n : ℤ => (1 / |(n : ℝ)|) ^ 2) := by
  have h0 := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  refine h0.congr (fun n => ?_)
  rw [div_pow, one_pow, sq_abs]

theorem inv_abs_sum_le (F : Finset ℤ) :
    ∑ n ∈ F, (1 / |(n : ℝ)|) ^ 2 ≤ ∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2 :=
  inv_abs_sq_summable.sum_le_tsum F (fun n _ => sq_nonneg _)

theorem inv_abs_tsum_nonneg : 0 ≤ ∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2 :=
  tsum_nonneg (fun n => sq_nonneg _)

end
end NlsGge.ThirdConsultation.KSPS017U0
