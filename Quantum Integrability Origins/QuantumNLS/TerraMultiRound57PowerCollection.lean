import QuantumNLS.TerraMultiRound57CoefficientUniqueness

/-! Finite reindexing of shifted powers into coefficient order. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound57PowerCollection

/-- Any finite family of shifted inverse-power polynomials can be collected
by exponent, with coefficients given by a finite sum and no convergence
assumptions. -/
theorem collect_shifted_powers {ι : Type} [DecidableEq ι] (S : Finset ι)
    (m : ι → ℕ) (shift : ι → ℕ) (c : ι → ℕ → ℂ) (N : ℕ)
    (hN : ∀ i ∈ S, ∀ j < m i, shift i + j < N) (Y : ℝ) :
    (∑ i ∈ S, ∑ j ∈ Finset.range (m i), (Y⁻¹ ^ (shift i + j)) • c i j) =
    ∑ n ∈ Finset.range N, (Y⁻¹ ^ n) •
      (∑ i ∈ S, ∑ j ∈ Finset.range (m i), if shift i + j = n then c i j else 0) := by
  classical
  simp_rw [Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hm : j < m i := Finset.mem_range.mp hj
  have hn : shift i + j ∈ Finset.range N := Finset.mem_range.mpr (hN i hi j hm)
  simp [Finset.sum_ite_eq', hn]

#print axioms collect_shifted_powers
end QuantumNLS.TerraMultiRound57PowerCollection
