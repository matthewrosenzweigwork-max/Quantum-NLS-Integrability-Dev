import QuantumNLS.TerraMultiRound63Division

/-! Match one term of the retained scalar expansion to finite division. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound64ExpansionTerm

theorem expansion_term (Y R : ℝ) (hY : Y ≠ 0) (j : ℕ) :
    Y * ((-1 : ℝ)^j * R * Y⁻¹^(2*j+1)) = (-(Y^2))⁻¹^j * R := by
  have hp : (-(Y^2))⁻¹^j = (-1 : ℝ)^j * (Y⁻¹^2)^j := by
    rw [inv_neg, neg_pow]
    simp only [← inv_pow]
  rw [hp, pow_add, pow_one, pow_mul]
  have hy : Y * Y⁻¹ = 1 := mul_inv_cancel₀ hY
  calc
    Y * ((-1 : ℝ)^j * R * ((Y⁻¹^2)^j * Y⁻¹)) =
      (Y * Y⁻¹) * ((-1 : ℝ)^j * (Y⁻¹^2)^j * R) := by ring
    _ = _ := by rw [hy, one_mul]

theorem expansion_sum (Y : ℝ) (hY : Y ≠ 0) (s : ℕ) (R : ℕ → ℝ)
    (hR0 : R 0 = 0) :
    Y * (∑ j ∈ Finset.Icc 1 s, (-1 : ℝ)^j * R j * Y⁻¹^(2*j+1)) =
      ∑ j ∈ Finset.range (s+1), (-(Y^2))⁻¹^j * R j := by
  rw [Finset.mul_sum]
  calc
    _ = ∑ j ∈ Finset.Icc 1 s, (-(Y^2))⁻¹^j * R j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact expansion_term Y (R j) hY j
    _ = _ := by
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        simp only [Finset.mem_range]
        omega
      · intro j hj hnot
        simp only [Finset.mem_range] at hj
        have hj0 : j = 0 := by
          simp only [Finset.mem_Icc, not_and_or] at hnot
          omega
        subst j
        simp [hR0]

#print axioms expansion_term
#print axioms expansion_sum
end QuantumNLS.TerraMultiRound64ExpansionTerm
