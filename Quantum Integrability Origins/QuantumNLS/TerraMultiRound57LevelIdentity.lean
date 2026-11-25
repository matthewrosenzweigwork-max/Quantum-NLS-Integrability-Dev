import QuantumNLS.TerraMultiRound56LevelCollection
import QuantumNLS.TerraMultiRound56FiniteRemainder

/-! Exact identification of the collected correlation remainders with the
physical finite tree levels. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound57LevelIdentity
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound51CorrelationExpansion
open QuantumNLS.TerraMultiRound51TaylorIntegral
open QuantumNLS.TerraMultiRound56LevelCollection
open QuantumNLS.TerraMultiRound56FiniteRemainder
open QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.TerraMultiRound45TreeSum
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

def positiveApprox {k : ℕ} (κ : ℝ) (u : Ell2) (n d : ℕ) (Y : ℝ) : ℂ :=
  ∑ t ∈ BinaryTree.treesOfNumNodesEq n,
    (-(κ : ℂ)) ^ t.numNodes * ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
      ∑ j ∈ Finset.range (d + 2), (Y⁻¹ ^ j) •
        integratedCoeff (Cfun (factorField (L := L) k u t)) (finiteFactorPaths t) j)

def leadingApprox {k : ℕ} (κ : ℝ) (u : Ell2) (n : ℕ) (Y : ℝ) : ℂ :=
  ∑ t ∈ BinaryTree.treesOfNumNodesEq n,
    (-(κ : ℂ)) ^ t.numNodes * ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
      Cfun (factorField (L := L) k u t) 0)

theorem positive_level_identity {k : ℕ} (hk : 1 ≤ k) (Y : ℝ) (hY : 0 < |Y|)
    (κ : ℝ) (u : Ell2) (n d : ℕ) :
    positiveRemainder (L := L) (k := k) κ u n d Y =
      scalar L k u (treeLevel (Fact.out : 0 < L) (a := (k : ℝ)) (by
        have h : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith) hY κ u n) - positiveApprox (L := L) (k := k) κ u n d Y := by
  rw [scalar_level_integrated hk Y hY κ u n]
  simp only [positiveRemainder, positiveApprox, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_inv]
  ring

theorem leading_level_identity {k : ℕ} (hk : 1 ≤ k) (Y : ℝ) (hY : 0 < |Y|)
    (κ : ℝ) (u : Ell2) (n : ℕ) :
    leadingRemainder (L := L) (k := k) κ u n Y =
      scalar L k u (treeLevel (Fact.out : 0 < L) (a := (k : ℝ)) (by
        have h : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith) hY κ u n) - leadingApprox (L := L) (k := k) κ u n Y := by
  rw [scalar_level_integrated hk Y hY κ u n]
  simp only [leadingRemainder, leadingApprox, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_inv]
  ring

#print axioms positive_level_identity
#print axioms leading_level_identity
end QuantumNLS.TerraMultiRound57LevelIdentity
