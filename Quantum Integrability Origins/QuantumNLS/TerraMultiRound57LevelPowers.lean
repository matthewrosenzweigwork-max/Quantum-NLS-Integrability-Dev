import QuantumNLS.TerraMultiRound57LevelIdentity
import QuantumNLS.TerraMultiRound57PowerCollection
import QuantumNLS.TerraMultiRound51TaylorLeading

/-! Put a tree level's correlation coefficients in inverse-power order. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound57LevelPowers
open QuantumNLS.TerraMultiRound53TreeIndex QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound51TaylorIntegral QuantumNLS.TerraMultiRound51TaylorLeading
open QuantumNLS.TerraMultiRound57LevelIdentity QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

def levelCoeff {k : ℕ} (κ : ℝ) (u : Ell2) (n j : ℕ) : ℂ :=
  ∑ t ∈ BinaryTree.treesOfNumNodesEq n,
    (-(κ : ℂ)) ^ t.numNodes * integratedCoeff
      (Cfun (factorField (L := L) k u t)) (finiteFactorPaths t) j

theorem positive_level_powers {k : ℕ} (κ : ℝ) (u : Ell2) (n d : ℕ) (Y : ℝ) :
    positiveApprox (L := L) (k := k) κ u n d Y =
      ∑ j ∈ Finset.range (d + 2), (Y⁻¹ ^ (2 * n + 1 + j)) • levelCoeff (L := L) (k := k) κ u n j := by
  unfold positiveApprox levelCoeff
  simp only [Finset.smul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := BinaryTree.mem_treesOfNumNodesEq.mp ht
  have he : Y⁻¹ ^ (2 * t.numNodes + 1) = Y⁻¹ ^ (2 * n + 1) := by rw [ht']
  rw [he]
  simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_inv, pow_add]
  push_cast
  ring

theorem leading_level_power {k : ℕ} (κ : ℝ) (u : Ell2) (n : ℕ) (Y : ℝ) :
    leadingApprox (L := L) (k := k) κ u n Y =
      (Y⁻¹ ^ (2 * n + 1)) • levelCoeff (L := L) (k := k) κ u n 0 := by
  unfold leadingApprox levelCoeff
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := BinaryTree.mem_treesOfNumNodesEq.mp ht
  have he : Y⁻¹ ^ (2 * t.numNodes + 1) = Y⁻¹ ^ (2 * n + 1) := by rw [ht']
  rw [he, integratedCoeff_zero]
  simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_inv]
  ring

#print axioms positive_level_powers
#print axioms leading_level_power
end QuantumNLS.TerraMultiRound57LevelPowers
