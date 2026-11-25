import QuantumNLS.TerraMultiRound46Root

/-! Finite tree-level recursion for the physical Riccati equation.
This is partial work toward REG-007. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound46Recursion
open Finset
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.TerraMultiRound45Trees
open QuantumNLS.TerraMultiRound45TreeSum QuantumNLS.TerraMultiRound46Root

/-- The ordered two-input nonlinear operation at the root. -/
def branch {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u x y : Ell2) : Ell2 :=
  -((κ / L : ℂ) • signedCLM L Y hY
    (mulBil hL ha (jEll u) (mulBil hL ha x y)))

/-- Exact finite Cauchy recursion for the level sums. -/
theorem tree_level_succ {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u : Ell2) (n : ℕ) :
    treeLevel hL ha hY κ u (n + 1) =
      ∑ ij ∈ antidiagonal n,
        branch hL ha hY κ u (treeLevel hL ha hY κ u ij.1)
          (treeLevel hL ha hY κ u ij.2) := by
  rw [tree_level_succ_root]
  apply sum_congr rfl
  rintro ⟨i, j⟩ hij
  simp only [branch, treeLevel, treeTerm, map_sum, Finset.smul_sum, Finset.sum_neg_distrib, ContinuousLinearMap.sum_apply]
  rw [Finset.sum_comm]

#print axioms tree_level_succ
end QuantumNLS.TerraMultiRound46Recursion
