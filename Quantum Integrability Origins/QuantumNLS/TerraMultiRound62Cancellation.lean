import QuantumNLS.TerraMultiRound61FiniteDivision

/-! Exact cancellation of the lower moments in a regularized difference. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound62Cancellation
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound61FiniteDivision

/-- The finite algebraic cancellation, independent of any limiting argument. -/
theorem recursive_cancellation (q : ℝ) (hq : q ≠ 0) (c : ℕ → ℝ) (d : ℕ → ℝ)
    (hd : ∀ n, d (n+1) = q * (c n - d n)) (s : ℕ) :
    d s - c s = (-q)^s * (d 0 - ∑ j ∈ Finset.range (s+1), (-q)⁻¹^j * c j) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [hd, Finset.sum_range_succ, pow_succ]
    have hq' : -q ≠ 0 := neg_ne_zero.mpr hq
    have hp : (-q)^s * ((-q)⁻¹)^s = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hq', one_pow]
    have hp' : (-q)^s * ((-q)⁻¹)^(s+1) = (-q)⁻¹ := by
      rw [pow_succ, ← mul_assoc, hp, one_mul]
    have hi : (-q) * (-q)⁻¹ = 1 := mul_inv_cancel₀ hq'
    have hterm : (-q)^s * (-q) * (((-q)⁻¹)^(s+1) * c (s+1)) = c (s+1) := by
      calc
        _ = ((-q) * ((-q)^s * ((-q)⁻¹)^(s+1))) * c (s+1) := by ring
        _ = c (s+1) := by rw [hp', hi, one_mul]
    calc
      q * (c s - d s) - c (s+1) = (-q) * (d s - c s) - c (s+1) := by ring
      _ = (-q) * ((-q)^s * (d 0 - ∑ j ∈ Finset.range (s+1), (-q)⁻¹^j * c j)) - c (s+1) := by rw [ih]
      _ = (-q)^s * (-q) * (d 0 - ((∑ j ∈ Finset.range (s+1), (-q)⁻¹^j * c j) +
          (-q)⁻¹^(s+1) * c (s+1))) +
          ((-q)^s * (-q) * ((-q)⁻¹^(s+1) * c (s+1)) - c (s+1)) := by ring
      _ = _ := by rw [hterm]; ring

/-- Apply the algebra to the actual integrals; lower moments are the only
integrability assumptions and no assertion about the highest moment is made. -/
theorem measure_cancellation (μ ν : Measure ℝ) (Y : ℝ) (hY : 0 < Y) (s : ℕ)
    (hμ : ∀ j < s, Integrable (fun t : ℝ => t ^ (2*j)) μ)
    (hν : ∀ j < s, Integrable (fun t : ℝ => t ^ (2*j)) ν) :
    let c : ℕ → ℝ := fun j => (∫ t : ℝ, t^(2*j) ∂μ) - (∫ t : ℝ, t^(2*j) ∂ν)
    ((∫ t, kernel s Y t ∂μ) - (∫ t, kernel s Y t ∂ν)) - c s =
      (-(Y^2))^s * (((∫ t, kernel 0 Y t ∂μ) - (∫ t, kernel 0 Y t ∂ν)) -
        ∑ j ∈ Finset.range (s+1), (-(Y^2))⁻¹^j * c j) := by
  dsimp only
  let c : ℕ → ℝ := fun j => (∫ t : ℝ, t^(2*j) ∂μ) - (∫ t : ℝ, t^(2*j) ∂ν)
  have hd : ∀ n, dividedDifference μ ν Y (n+1) = Y^2 * (c n - dividedDifference μ ν Y n) := by
    intro n
    dsimp [dividedDifference, c]
    ring
  have h := recursive_cancellation (Y^2) (by positivity) c (dividedDifference μ ν Y) hd s
  rw [finite_division μ ν Y hY s hμ hν] at h
  exact h

#print axioms recursive_cancellation
#print axioms measure_cancellation
end QuantumNLS.TerraMultiRound62Cancellation
