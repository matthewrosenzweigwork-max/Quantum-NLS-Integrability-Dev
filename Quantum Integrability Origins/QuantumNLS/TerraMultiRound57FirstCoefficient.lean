import QuantumNLS.TerraMultiRound57CollectedPowers

/-! Isolate the first nonlinear tree coefficient. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound57FirstCoefficient
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.TerraMultiRound57LevelPowers QuantumNLS.TerraMultiRound57CollectedPowers
variable {L : ℝ} [Fact (0 < L)]

theorem tree_coefficients_below_three {k : ℕ} (κ : ℝ) (u : Ell2) (s n : ℕ) (hn : n < 3) :
    treeCoefficient (L := L) (k := k) κ u s n = 0 := by
  unfold treeCoefficient
  apply Finset.sum_eq_zero
  intro ell hell
  apply Finset.sum_eq_zero
  intro j hj
  have he := Finset.mem_Ico.mp hell
  simp only [if_neg (show 2 * ell + 1 + j ≠ n by omega)]

/-- The inverse-cube coefficient is exactly the leading one-node level. -/
theorem tree_coefficient_three {k : ℕ} (κ : ℝ) (u : Ell2) (s : ℕ) (hs : 1 ≤ s) :
    treeCoefficient (L := L) (k := k) κ u s 3 = levelCoeff (L := L) (k := k) κ u 1 0 := by
  unfold treeCoefficient
  rw [Finset.sum_eq_single 1]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro j hj hj0
      have hj' : 0 < j := Nat.pos_of_ne_zero hj0
      simp only [if_neg (show 2 * 1 + 1 + j ≠ 3 by omega)]
    · intro h
      have hm : 0 < 2 * (s - 1) + 1 := by omega
      exact (h (Finset.mem_range.mpr hm)).elim
  · intro ell hell hell1
    have he := Finset.mem_Ico.mp hell
    have he2 : 2 ≤ ell := by omega
    apply Finset.sum_eq_zero
    intro j hj
    simp only [if_neg (show 2 * ell + 1 + j ≠ 3 by omega)]
  · intro h
    have hm : 1 ∈ Finset.Ico 1 (s + 1) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    exact (h hm).elim

#print axioms tree_coefficients_below_three
#print axioms tree_coefficient_three
end QuantumNLS.TerraMultiRound57FirstCoefficient
