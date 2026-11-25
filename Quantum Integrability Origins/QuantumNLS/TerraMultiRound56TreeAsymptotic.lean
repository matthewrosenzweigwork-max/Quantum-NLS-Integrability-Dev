import QuantumNLS.TerraMultiRound56CorrelationBridge

/-! Transport one tree's correlation remainder with its physical prefactor. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound56TreeAsymptotic
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound51CorrelationExpansion
open QuantumNLS.TerraMultiRound51TaylorIntegral
open QuantumNLS.TerraMultiRound52InverseScale
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

/-- A positive-degree expansion for a single physical tree contribution;
the fixed-field little-oh includes all powers from the resolvent prefactor. -/
theorem weighted_tree_remainder {k d : ℕ} (hk : 1 ≤ k) (hd : d + 1 ≤ 2 * k)
    (κ : ℝ) (u : Ell2) (t : BinaryTree Unit) :
    (fun Y : ℝ => (-(κ : ℂ)) ^ t.numNodes *
      ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
        (integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k u t)
          (finiteFactorPaths t) Y⁻¹ -
        ∑ j ∈ Finset.range (d + 2), (Y⁻¹ ^ j) •
          integratedCoeff (Cfun (factorField (L := L) k u t)) (finiteFactorPaths t) j)))
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * t.numNodes + 1 + (d + 1))) := by
  have h := correlation_expansion_atTop hk (factorField (L := L) k u t) hd (finiteFactorPaths t)
  have hm := (isBigO_refl (fun Y : ℝ => Y⁻¹ ^ (2 * t.numNodes + 1)) atTop).smul_isLittleO h
  have hc := hm.const_mul_left ((-(κ : ℂ)) ^ t.numNodes)
  simpa only [smul_eq_mul, ← pow_add] using hc

#print axioms weighted_tree_remainder
end QuantumNLS.TerraMultiRound56TreeAsymptotic
