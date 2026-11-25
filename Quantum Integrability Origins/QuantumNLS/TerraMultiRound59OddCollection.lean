import Mathlib

/-! Collect a finite sequence whose even-indexed entries vanish. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59OddCollection

theorem sum_odd (s : ℕ) (f : ℕ → ℝ) (h0 : f 0 = 0)
    (he : ∀ m : ℕ, 2 * m + 2 ≤ 2 * s + 1 → f (2 * m + 2) = 0) :
    ∑ n ∈ Finset.range (2 * s + 2), f n =
      ∑ j ∈ Finset.range (s + 1), f (2 * j + 1) := by
  induction s with
  | zero => simp [Finset.sum_range_succ, h0]
  | succ s ih =>
    have he' : ∀ m : ℕ, 2 * m + 2 ≤ 2 * s + 1 → f (2 * m + 2) = 0 := by
      intro m hm
      exact he m (by omega)
    have hz : f (2 * s + 2) = 0 := he s (by omega)
    have hsize : 2 * (s + 1) + 2 = (2 * s + 2) + 2 := by omega
    rw [hsize, Finset.sum_range_succ, Finset.sum_range_succ, ih he', hz]
    simp only [add_zero]
    have heq : 2 * s + 2 + 1 = 2 * (s + 1) + 1 := by omega
    rw [heq]
    simp only [Finset.sum_range_succ]

#print axioms sum_odd
end QuantumNLS.TerraMultiRound59OddCollection
