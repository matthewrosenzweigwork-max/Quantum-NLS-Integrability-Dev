import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB1Lattice

/-! # Track B, step B1: the resonance sum in the `X^{0,a} → L⁴` argument

Pro report, proof of `X^{0,a} ↪ L⁴`: after Cauchy–Schwarz and (timeconv), the reciprocal-weight
factor is `C Σ_k ⟨τ + (2πk)² + (2π(n-k))²⟩^{1-4a}`, and completing the square
`(2πk)² + (2π(n-k))² = 8π²(k - n/2)² + 2π²n²` reduces it to (latticesum).
This module proves the resulting uniform bound over all real `τ` and all integers `n`,
with `a = 13/32`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

/-- The completed square `(2πk)² + (2π(n-k))² = 8π²(k - n/2)² + 2π²n²`. -/
theorem complete_square_two_pi (n k : ℝ) :
    (2 * Real.pi * k) ^ 2 + (2 * Real.pi * (n - k)) ^ 2 =
      8 * Real.pi ^ 2 * (k - n / 2) ^ 2 + 2 * Real.pi ^ 2 * n ^ 2 := by
  ring

/-- **Uniform resonance sum** (`a = 13/32`): one constant bounds, for every real `τ` and every
integer `n`, the convergent series `Σ_k ⟨τ + (2πk)² + (2π(n-k))²⟩^{1-4a}`. -/
theorem resonance_sum_bound_pro :
    ∃ C : ℝ, ∀ (τ : ℝ) (n : ℤ),
      Summable (fun k : ℤ =>
        brk (τ + (2 * Real.pi * k) ^ 2 + (2 * Real.pi * ((n : ℝ) - k)) ^ 2) ^
          (1 - 4 * (13 / 32 : ℝ))) ∧
        ∑' k : ℤ, brk (τ + (2 * Real.pi * k) ^ 2 + (2 * Real.pi * ((n : ℝ) - k)) ^ 2) ^
          (1 - 4 * (13 / 32 : ℝ)) ≤ C := by
  obtain ⟨C, hC⟩ := lattice_sum_bound_pro
  refine ⟨C, fun τ n => ?_⟩
  have hfun : (fun k : ℤ =>
      brk (τ + (2 * Real.pi * k) ^ 2 + (2 * Real.pi * ((n : ℝ) - k)) ^ 2) ^
        (1 - 4 * (13 / 32 : ℝ))) =
      fun k : ℤ => brk ((τ + 2 * Real.pi ^ 2 * (n : ℝ) ^ 2) +
        8 * Real.pi ^ 2 * ((k : ℝ) - (n : ℝ) / 2) ^ 2) ^ (-(4 * (13 / 32 : ℝ) - 1)) := by
    funext k
    rw [show (1 : ℝ) - 4 * (13 / 32 : ℝ) = -(4 * (13 / 32 : ℝ) - 1) by ring]
    congr 2
    have := complete_square_two_pi (n : ℝ) (k : ℝ)
    linarith
  rw [hfun]
  exact hC _ _

end LiebLiniger.FixedPeriod.ALLS.PdeB
