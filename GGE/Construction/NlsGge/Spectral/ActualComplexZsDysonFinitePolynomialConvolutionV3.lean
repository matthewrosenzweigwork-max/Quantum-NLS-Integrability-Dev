import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

theorem actualComplexZsDyson_finite_polynomial_convolution
    (n : ℕ) (z a b : ℂ) (c : ℕ → ℂ)
    (hsupport : ∀ k, n < k → c k = 0) :
    (∑ k ∈ Finset.range (n + 2),
      z ^ k * (a * c k + if k = 0 then 0 else b * c (k - 1))) =
      (a + z * b) * (∑ k ∈ Finset.range (n + 1), z ^ k * c k) := by
  have hcn1 : c (n + 1) = 0 := hsupport (n + 1) (by omega)
  have ha :
      (∑ k ∈ Finset.range (n + 2), z ^ k * (a * c k)) =
        a * (∑ k ∈ Finset.range (n + 1), z ^ k * c k) := by
    rw [Finset.sum_range_succ]
    simp only [hcn1, mul_zero, add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hb :
      (∑ k ∈ Finset.range (n + 2),
        z ^ k * (if k = 0 then 0 else b * c (k - 1))) =
        (z * b) * (∑ k ∈ Finset.range (n + 1), z ^ k * c k) := by
    rw [Finset.sum_range_succ']
    simp [Nat.add_sub_cancel, pow_succ]
    calc
      (∑ k ∈ Finset.range (n + 1),
          z ^ (k + 1) * (b * c ((k + 1) - 1))) =
          ∑ k ∈ Finset.range (n + 1), (z * b) * (z ^ k * c k) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Nat.add_sub_cancel, pow_succ]
        ring
      _ = (z * b) * (∑ k ∈ Finset.range (n + 1), z ^ k * c k) := by
        rw [Finset.mul_sum]
  calc
    (∑ k ∈ Finset.range (n + 2),
        z ^ k * (a * c k + if k = 0 then 0 else b * c (k - 1))) =
        (∑ k ∈ Finset.range (n + 2), z ^ k * (a * c k)) +
          (∑ k ∈ Finset.range (n + 2),
            z ^ k * (if k = 0 then 0 else b * c (k - 1))) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    _ = (a + z * b) * (∑ k ∈ Finset.range (n + 1), z ^ k * c k) := by
      rw [ha, hb]
      ring

end NlsGge.SpectralFoundations
