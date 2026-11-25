import QuantumNLS.TerraMultiRound56ScalarBridge
import QuantumNLS.TerraMultiRound52InverseScale

/-! Exact link from a physical scalar tree to the expansion interface. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound56CorrelationBridge
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound56ScalarBridge
open QuantumNLS.TerraMultiRound51CorrelationExpansion
open QuantumNLS.TerraMultiRound52InverseScale
open QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.RiccatiSobolevBanach

variable {L : ℝ} [Fact (0 < L)]

/-- A scalar tree is exactly the inverse-scale integrated correlation,
with its complete physical normalization. -/
theorem scalar_tree_integrated {k : ℕ} (hk : 1 ≤ k) (Y : ℝ) (hY : 0 < |Y|)
    (κ : ℝ) (u : Ell2) (t : BinaryTree Unit) :
    scalar L (k : ℝ) u (QuantumNLS.TerraMultiRound45Trees.treeTerm (a := (k : ℝ))
      (Fact.out : 0 < L) (by
        have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith) hY κ u t) =
      (-(κ : ℂ)) ^ t.numNodes * (Y⁻¹ : ℂ) ^ (2 * t.numNodes + 1) *
        integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k u t)
          (finiteFactorPaths t) Y⁻¹ := by
  rw [scalar_tree_flat hk]
  congr 1

#print axioms scalar_tree_integrated
end QuantumNLS.TerraMultiRound56CorrelationBridge
