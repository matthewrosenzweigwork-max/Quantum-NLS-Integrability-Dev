import QuantumNLS.TerraMultiRound57CollectedPowers

/-! Stability of retained coefficients when the finite tree truncation is enlarged. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59TreeOrder
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.TerraMultiRound57LevelPowers

variable {L : ℝ} [Fact (0 < L)]

theorem tree_coefficient_truncation_stable {k : ℕ} (κ : ℝ) (x : Ell2)
    (s t n : ℕ) (hst : s ≤ t) (hn : n ≤ 2 * s + 1) :
    treeCoefficient (L := L) (k := k) κ x s n = treeCoefficient (L := L) (k := k) κ x t n := by
  unfold treeCoefficient
  calc
    _ = ∑ ell ∈ Finset.Ico 1 (s + 1), ∑ d ∈ Finset.range (2 * (t - ell) + 1),
        if 2 * ell + 1 + d = n then levelCoeff (L := L) (k := k) κ x ell d else 0 := by
      apply Finset.sum_congr rfl
      intro ell hell
      apply Finset.sum_subset
      · intro d hd
        simp only [Finset.mem_range] at *
        omega
      · intro d hd hnot
        have he := Finset.mem_Ico.mp hell
        have hd' := Finset.mem_range.mp hd
        have hnot' : ¬d < 2 * (s - ell) + 1 := by simpa using hnot
        have hne : 2 * ell + 1 + d ≠ n := by omega
        simp [hne]
    _ = _ := by
      apply Finset.sum_subset
      · intro ell hell
        simp only [Finset.mem_Ico] at *
        omega
      · intro ell hell hnot
        have he := Finset.mem_Ico.mp hell
        have hnot' : ¬(1 ≤ ell ∧ ell < s + 1) := by simpa using hnot
        apply Finset.sum_eq_zero
        intro d hd
        have hne : 2 * ell + 1 + d ≠ n := by omega
        simp [hne]

#print axioms tree_coefficient_truncation_stable
end QuantumNLS.TerraMultiRound59TreeOrder
