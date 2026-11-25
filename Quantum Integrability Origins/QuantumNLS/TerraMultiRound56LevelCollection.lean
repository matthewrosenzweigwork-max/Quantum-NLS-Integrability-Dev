import QuantumNLS.TerraMultiRound56CorrelationBridge
import QuantumNLS.TerraMultiRound45ScalarBound
import QuantumNLS.TerraMultiRound46Root

/-! Exact finite tree-level collection, retaining the linear term. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound56LevelCollection
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound56CorrelationBridge
open QuantumNLS.TerraMultiRound51CorrelationExpansion
open QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.TerraMultiRound45ScalarBound
open QuantumNLS.TerraMultiRound45TreeSum
open QuantumNLS.TerraMultiRound46Root
open QuantumNLS.TerraMultiRound38SignedPicard
open QuantumNLS.RiccatiSobolevBanach

variable {L : ℝ} [Fact (0 < L)]

theorem scalar_add (L : ℝ) (hL : 0 < L) {a : ℝ} (ha : 1 / 2 < a)
    (u v w : Ell2) : scalar L a u (v + w) = scalar L a u v + scalar L a u w := by
  have h := scalar_sub L hL ha u (v + w) w
  simp only [add_sub_cancel_right] at h
  exact (eq_sub_iff_add_eq.mp h).symm

theorem scalar_zero (L : ℝ) (hL : 0 < L) {a : ℝ} (ha : 1 / 2 < a)
    (u : Ell2) : scalar L a u 0 = 0 := by
  have h := scalar_sub L hL ha u (0 : Ell2) 0
  simpa only [sub_self] using h

theorem scalar_sum {ι : Type} (L : ℝ) (hL : 0 < L) {a : ℝ} (ha : 1 / 2 < a)
    (u : Ell2) (S : Finset ι) (f : ι → Ell2) :
    scalar L a u (∑ i ∈ S, f i) = ∑ i ∈ S, scalar L a u (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [scalar_zero L hL ha]
  | @insert i S hi ih => simp [hi, scalar_add L hL ha, ih]

/-- The zero tree level is the exact free-resolvent pairing. -/
theorem scalar_level_zero {a Y : ℝ} (ha : 1 / 2 < a) (hY : 0 < |Y|)
    (κ : ℝ) (u : Ell2) :
    scalar L a u (treeLevel (Fact.out : 0 < L) ha hY κ u 0) =
      scalar L a u (signedCLM L Y hY u) := by
  rw [tree_level_zero]

/-- The scalar of a finite tree level is precisely the finite sum of its
physically normalized integrated correlations. -/
theorem scalar_level_integrated {k : ℕ} (hk : 1 ≤ k) (Y : ℝ) (hY : 0 < |Y|)
    (κ : ℝ) (u : Ell2) (n : ℕ) :
    scalar L (k : ℝ) u (treeLevel (Fact.out : 0 < L) (a := (k : ℝ)) (by
      have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith) hY κ u n) =
      ∑ t ∈ BinaryTree.treesOfNumNodesEq n,
        (-(κ : ℂ)) ^ t.numNodes * (Y⁻¹ : ℂ) ^ (2 * t.numNodes + 1) *
          integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k u t)
            (finiteFactorPaths t) Y⁻¹ := by
  have ha : (1 : ℝ) / 2 < (k : ℝ) := by
    have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  unfold treeLevel
  rw [scalar_sum L (Fact.out : 0 < L) ha]
  apply Finset.sum_congr rfl
  intro t ht
  exact scalar_tree_integrated hk Y hY κ u t

#print axioms scalar_add
#print axioms scalar_zero
#print axioms scalar_sum
#print axioms scalar_level_zero
#print axioms scalar_level_integrated
end QuantumNLS.TerraMultiRound56LevelCollection
