import Mathlib

/- KSPS011Q5C PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS011Quant5Core.lean. Pure finite-sum lemmas (no project imports):
   (a+…+f)² ≤ 6(a²+…+f²) and its finite-sum form, and finite sums of a summable nonnegative sequence ≤ its tsum. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPSQ5C

theorem sq_add6_le (a b c d e f : ℝ) :
    (a + b + c + d + e + f) ^ 2 ≤ 6 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (a - f),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (b - f), sq_nonneg (c - d),
    sq_nonneg (c - e), sq_nonneg (c - f), sq_nonneg (d - e), sq_nonneg (d - f), sq_nonneg (e - f)]

theorem sum_sq_le_six {ι : Type*} (F : Finset ι) (x t1 t2 t3 t4 t5 t6 : ι → ℝ)
    (h : ∀ n ∈ F, 0 ≤ x n ∧ x n ≤ t1 n + t2 n + t3 n + t4 n + t5 n + t6 n)
    (T1 T2 T3 T4 T5 T6 : ℝ)
    (h1 : ∑ n ∈ F, t1 n ^ 2 ≤ T1) (h2 : ∑ n ∈ F, t2 n ^ 2 ≤ T2) (h3 : ∑ n ∈ F, t3 n ^ 2 ≤ T3)
    (h4 : ∑ n ∈ F, t4 n ^ 2 ≤ T4) (h5 : ∑ n ∈ F, t5 n ^ 2 ≤ T5) (h6 : ∑ n ∈ F, t6 n ^ 2 ≤ T6) :
    ∑ n ∈ F, x n ^ 2 ≤ 6 * (T1 + T2 + T3 + T4 + T5 + T6) := by
  have hp : ∀ n ∈ F, x n ^ 2 ≤
      6 * (t1 n ^ 2 + t2 n ^ 2 + t3 n ^ 2 + t4 n ^ 2 + t5 n ^ 2 + t6 n ^ 2) := by
    intro n hn
    obtain ⟨h0, hle⟩ := h n hn
    exact (pow_le_pow_left₀ h0 hle 2).trans (sq_add6_le _ _ _ _ _ _)
  refine (Finset.sum_le_sum hp).trans ?_
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  linarith

theorem sum_le_tsum_of_nonneg {f : ℤ → ℝ} (h0 : ∀ n, 0 ≤ f n) (hs : Summable f) (F : Finset ℤ) :
    ∑ n ∈ F, f n ≤ ∑' n, f n :=
  hs.sum_le_tsum F (fun n _ => h0 n)

end NlsGge.ThirdConsultation.KSPSQ5C
