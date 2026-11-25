import QuantumNLS.TerraMultiRound56LevelAsymptotic
import QuantumNLS.TerraMultiRound52InverseScale

/-! The degree-zero case for a finite tree level. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound56LevelLeading
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound51CorrelationExpansion
open QuantumNLS.TerraMultiRound52InverseScale
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

/-- For each fixed level the leading correlation has a little-oh remainder,
including when no positive Taylor degree is available. -/
theorem level_leading_remainder {k : ℕ} (hk : 1 ≤ k)
    (κ : ℝ) (u : Ell2) (n : ℕ) :
    (fun Y : ℝ => ∑ t ∈ BinaryTree.treesOfNumNodesEq n,
      (-(κ : ℂ)) ^ t.numNodes * ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
        (integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k u t)
          (finiteFactorPaths t) Y⁻¹ - Cfun (factorField (L := L) k u t) 0)))
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * n + 1)) := by
  have h : ∀ t ∈ BinaryTree.treesOfNumNodesEq n,
      (fun Y : ℝ => (-(κ : ℂ)) ^ t.numNodes * ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
        (integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k u t)
          (finiteFactorPaths t) Y⁻¹ - Cfun (factorField (L := L) k u t) 0)))
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * n + 1)) := by
    intro t ht
    have ht' : t.numNodes = n := BinaryTree.mem_treesOfNumNodesEq.mp ht
    have h0 : (fun Y : ℝ => integratedCorrelation (m := 2 * t.numNodes)
        (factorField (L := L) k u t) (finiteFactorPaths t) Y⁻¹ -
        Cfun (factorField (L := L) k u t) 0) =o[atTop] (fun _ : ℝ => (1 : ℝ)) := by
      apply (isLittleO_one_iff ℝ).2
      have hcst : Tendsto (fun _ : ℝ => Cfun (factorField (L := L) k u t) 0)
          atTop (𝓝 (Cfun (factorField (L := L) k u t) 0)) := tendsto_const_nhds
      simpa only [sub_self] using
        (correlation_leading_atTop hk (factorField (L := L) k u t) (finiteFactorPaths t)).sub hcst
    have hm := (isBigO_refl (fun Y : ℝ => Y⁻¹ ^ (2 * t.numNodes + 1)) atTop).smul_isLittleO h0
    have hc := hm.const_mul_left ((-(κ : ℂ)) ^ t.numNodes)
    have he : (fun Y : ℝ => Y⁻¹ ^ (2 * t.numNodes + 1)) =
        (fun Y : ℝ => Y⁻¹ ^ (2 * n + 1)) := by rw [ht']
    rw [← he]
    simpa only [smul_eq_mul, mul_one] using hc
  convert IsLittleO.sum h using 1
  funext Y
  simp only [Finset.sum_apply]

#print axioms level_leading_remainder
end QuantumNLS.TerraMultiRound56LevelLeading
