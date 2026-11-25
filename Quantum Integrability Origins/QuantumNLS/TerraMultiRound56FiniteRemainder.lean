import QuantumNLS.TerraMultiRound56LevelLeading

/-! Collect the fixed-field correlation remainders through a Sobolev order. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound56FiniteRemainder
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound51CorrelationExpansion
open QuantumNLS.TerraMultiRound51TaylorIntegral
open QuantumNLS.TerraMultiRound56LevelAsymptotic
open QuantumNLS.TerraMultiRound56LevelLeading
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

def positiveRemainder {k : ℕ} (κ : ℝ) (u : Ell2) (n d : ℕ) (Y : ℝ) : ℂ :=
  ∑ t ∈ BinaryTree.treesOfNumNodesEq n,
    (-(κ : ℂ)) ^ t.numNodes * ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
      (integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k u t)
        (finiteFactorPaths t) Y⁻¹ -
      ∑ j ∈ Finset.range (d + 2), (Y⁻¹ ^ j) •
        integratedCoeff (Cfun (factorField (L := L) k u t)) (finiteFactorPaths t) j))

def leadingRemainder {k : ℕ} (κ : ℝ) (u : Ell2) (n : ℕ) (Y : ℝ) : ℂ :=
  ∑ t ∈ BinaryTree.treesOfNumNodesEq n,
    (-(κ : ℂ)) ^ t.numNodes * ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
      (integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k u t)
        (finiteFactorPaths t) Y⁻¹ - Cfun (factorField (L := L) k u t) 0))

/-- The sum over levels one through s has the claimed common fixed-field
little-oh power. The last level uses the separate degree-zero theorem. -/
theorem finite_tree_remainders (s : ℕ) (hs : 2 ≤ s) (κ : ℝ) (u : Ell2) :
    (fun Y : ℝ => (∑ n ∈ Finset.Ico 1 s,
      positiveRemainder (L := L) (k := s - 1) κ u n (2 * (s - n) - 1) Y) +
      leadingRemainder (L := L) (k := s - 1) κ u s Y)
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1)) := by
  have hk : 1 ≤ s - 1 := by omega
  have hp : ∀ n ∈ Finset.Ico 1 s,
      (fun Y : ℝ => positiveRemainder (L := L) (k := s - 1) κ u n (2 * (s - n) - 1) Y)
        =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1)) := by
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hd : (2 * (s - n) - 1) + 1 ≤ 2 * (s - 1) := by omega
    have he : 2 * n + 1 + ((2 * (s - n) - 1) + 1) = 2 * s + 1 := by omega
    have h := level_remainder (L := L) hk hd κ u n
    rw [he] at h
    exact h
  have hsum : (fun Y : ℝ => ∑ n ∈ Finset.Ico 1 s,
      positiveRemainder (L := L) (k := s - 1) κ u n (2 * (s - n) - 1) Y)
        =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1)) := by
    convert IsLittleO.sum hp using 1
    funext Y
    simp only [Finset.sum_apply]
  have hlast := level_leading_remainder (L := L) hk κ u s
  exact hsum.add hlast

#print axioms finite_tree_remainders
end QuantumNLS.TerraMultiRound56FiniteRemainder
