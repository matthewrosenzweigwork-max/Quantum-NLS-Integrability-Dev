import QuantumNLS.TerraMultiRound56TreeAsymptotic

/-! Finite collection of the positive-degree remainders at one tree level. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound56LevelAsymptotic
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound51CorrelationExpansion
open QuantumNLS.TerraMultiRound51TaylorIntegral
open QuantumNLS.TerraMultiRound56TreeAsymptotic
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

/-- At a fixed level the finite sum of the individually controlled
positive-degree remainders retains the same little-oh power. -/
theorem level_remainder {k d : ℕ} (hk : 1 ≤ k) (hd : d + 1 ≤ 2 * k)
    (κ : ℝ) (u : Ell2) (n : ℕ) :
    (fun Y : ℝ => ∑ t ∈ BinaryTree.treesOfNumNodesEq n,
      (-(κ : ℂ)) ^ t.numNodes * ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
        (integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k u t)
          (finiteFactorPaths t) Y⁻¹ -
        ∑ j ∈ Finset.range (d + 2), (Y⁻¹ ^ j) •
          integratedCoeff (Cfun (factorField (L := L) k u t)) (finiteFactorPaths t) j)))
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * n + 1 + (d + 1))) := by
  have h : ∀ t ∈ BinaryTree.treesOfNumNodesEq n,
      (fun Y : ℝ => (-(κ : ℂ)) ^ t.numNodes * ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
        (integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k u t)
          (finiteFactorPaths t) Y⁻¹ -
        ∑ j ∈ Finset.range (d + 2), (Y⁻¹ ^ j) •
          integratedCoeff (Cfun (factorField (L := L) k u t)) (finiteFactorPaths t) j)))
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * n + 1 + (d + 1))) := by
    intro t ht
    have ht' : t.numNodes = n := BinaryTree.mem_treesOfNumNodesEq.mp ht
    have he : (fun Y : ℝ => Y⁻¹ ^ (2 * t.numNodes + 1 + (d + 1))) =
        (fun Y : ℝ => Y⁻¹ ^ (2 * n + 1 + (d + 1))) := by rw [ht']
    rw [← he]
    exact weighted_tree_remainder hk hd κ u t
  convert IsLittleO.sum h using 1
  funext Y
  simp only [Finset.sum_apply]

#print axioms level_remainder
end QuantumNLS.TerraMultiRound56LevelAsymptotic
