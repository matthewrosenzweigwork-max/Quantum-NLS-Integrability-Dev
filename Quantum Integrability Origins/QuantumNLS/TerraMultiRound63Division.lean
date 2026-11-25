import QuantumNLS.TerraMultiRound62Cancellation

/-! Exact extraction of the next regularized term from its lower moments. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound63Division
open QuantumNLS.TerraMultiRound62Cancellation

theorem recursive_division (q : ℝ) (hq : q ≠ 0) (c d : ℕ → ℝ)
    (hd : ∀ n, d (n+1) = q * (c n - d n)) (s : ℕ) :
    d (s+1) = (-q)^(s+1) *
      (d 0 - ∑ j ∈ Finset.range (s+1), (-q)⁻¹^j * c j) := by
  have h := recursive_cancellation q hq c d hd s
  rw [hd, show c s - d s = -(d s - c s) by ring, h, pow_succ]
  ring

theorem correction_from_expansion (q : ℝ) (hq : q ≠ 0) (c d : ℕ → ℝ)
    (hd : ∀ n, d (n+1) = q * (c n - d n)) (s : ℕ) (R e : ℝ)
    (hexp : d 0 - ∑ j ∈ Finset.range (s+1), (-q)⁻¹^j * c j =
      (-q)⁻¹^(s+1) * R + e) :
    d (s+1) = R + (-q)^(s+1) * e := by
  have hp : (-q)^(s+1) * ((-q)⁻¹)^(s+1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (neg_ne_zero.mpr hq), one_pow]
  rw [recursive_division q hq c d hd s, hexp, mul_add, ← mul_assoc, hp, one_mul]

#print axioms recursive_division
#print axioms correction_from_expansion
end QuantumNLS.TerraMultiRound63Division
