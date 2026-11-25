import QuantumNLS.TerraMultiRound57LevelPowers

/-! Collect all positive tree levels by inverse power. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.TerraMultiRound57LevelIdentity QuantumNLS.TerraMultiRound57LevelPowers
open QuantumNLS.TerraMultiRound57PowerCollection

variable {L : ℝ} [Fact (0 < L)]

def treeCoefficient {k : ℕ} (κ : ℝ) (u : Ell2) (s n : ℕ) : ℂ :=
  ∑ ell ∈ Finset.Ico 1 (s + 1), ∑ j ∈ Finset.range (2 * (s - ell) + 1),
    if 2 * ell + 1 + j = n then levelCoeff (L := L) (k := k) κ u ell j else 0

/-- The explicit correlation approximants collect into a single inverse-power
polynomial. The free resolvent remains separate and exact. -/
theorem collect_tree_powers {k : ℕ} (s : ℕ) (hs : 2 ≤ s) (κ : ℝ) (u : Ell2) (Y : ℝ) :
    (∑ ell ∈ Finset.Ico 1 s,
      positiveApprox (L := L) (k := k) κ u ell (2 * (s - ell) - 1) Y) +
      leadingApprox (L := L) (k := k) κ u s Y =
    ∑ n ∈ Finset.range (2 * s + 2), (Y⁻¹ ^ n) • treeCoefficient (L := L) (k := k) κ u s n := by
  let S := Finset.Ico 1 (s + 1)
  let m : ℕ → ℕ := fun ell => 2 * (s - ell) + 1
  let shift : ℕ → ℕ := fun ell => 2 * ell + 1
  have hN : ∀ ell ∈ S, ∀ j < m ell, shift ell + j < 2 * s + 2 := by
    intro ell hell j hj
    have he := Finset.mem_Ico.mp hell
    dsimp [m, shift] at *
    omega
  have hc := collect_shifted_powers S m shift (fun ell j => levelCoeff (L := L) (k := k) κ u ell j) (2 * s + 2) hN Y
  have hleft : (∑ ell ∈ S, ∑ j ∈ Finset.range (m ell),
      (Y⁻¹ ^ (shift ell + j)) • levelCoeff (L := L) (k := k) κ u ell j) =
      (∑ ell ∈ Finset.Ico 1 s, positiveApprox (L := L) (k := k) κ u ell (2 * (s - ell) - 1) Y) +
      leadingApprox (L := L) (k := k) κ u s Y := by
    dsimp [S]
    rw [Finset.sum_Ico_succ_top (show 1 ≤ s by omega)]
    congr 1
    · apply Finset.sum_congr rfl
      intro ell hell
      have he := Finset.mem_Ico.mp hell
      rw [positive_level_powers]
      have hd : (2 * (s - ell) - 1) + 2 = 2 * (s - ell) + 1 := by omega
      simp only [hd]
      rfl
    · rw [leading_level_power]
      simp [m, shift]
  rw [hleft] at hc
  simpa [S, m, shift, treeCoefficient] using hc

#print axioms collect_tree_powers
end QuantumNLS.TerraMultiRound57CollectedPowers
