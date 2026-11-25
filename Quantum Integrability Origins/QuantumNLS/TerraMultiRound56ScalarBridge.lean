import QuantumNLS.TerraMultiRound56TreeBridge
import QuantumNLS.TerraMultiRound40ScalarParity

/-! Scalar pairing of a tree and its flat path correlation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound56ScalarBridge
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound53TreeFactor
open QuantumNLS.TerraMultiRound48TreeFubini
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound56KernelSplit
open QuantumNLS.TerraMultiRound56FlatRecursion
open QuantumNLS.TerraMultiRound56TreeBridge
open QuantumNLS.TerraMultiRound49SobolevBridge
open QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

/-- Exact scalar-to-flat-correlation bridge, including the physical coupling
and every resolvent factor. -/
theorem scalar_tree_flat {k : ℕ} (hk : 1 ≤ k) (Y : ℝ) (hY : 0 < |Y|)
    (κ : ℝ) (u : Ell2) (t : BinaryTree Unit) :
    scalar L (k : ℝ) u (QuantumNLS.TerraMultiRound45Trees.treeTerm (a := (k : ℝ))
      (Fact.out : 0 < L) (by
        have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith) hY κ u t) =
      (-(κ : ℂ)) ^ t.numNodes * (Y⁻¹ : ℂ) ^ (2 * t.numNodes + 1) *
        (∫ time, ((∏ i, Real.exp (-time i) : ℝ) : ℂ) *
          Cfun (factorField (L := L) k u t) (pathShift (finiteFactorPaths t) Y time) ∂
          (Measure.pi (fun _ : Fin (2 * t.numNodes + 1) => volume.restrict (Ioi (0 : ℝ))))) := by
  have ha : (1 : ℝ) / 2 < (k : ℝ) := by
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  let tree := QuantumNLS.TerraMultiRound45Trees.treeTerm (Fact.out : 0 < L) ha hY κ u t
  let outer := contRep hk (physicalToHk (L := L) k (QuantumNLS.ComplexifiedSobolevField.jEll u))
  let field := contRep hk (physicalToHk (L := L) k tree)
  have hs : scalar L (k : ℝ) u tree = ∫ x : AddCircle L, outer x * field x := by
    rw [← AddCircle.intervalIntegral_preimage L 0 (fun x => outer x * field x)]
    simp only [zero_add]
    unfold scalar
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [outer, field, physicalToHk_rep, QuantumNLS.RiccatiExpansions.physRep_jEll]
  change scalar L (k : ℝ) u tree = _
  rw [hs, ← tree_fubini hk, integral_prod_symm _ (physical_kernel_integrable hk u t Y)]
  simp_rw [treeIntegrand_eq_outer_mul hk, integral_const_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have hfield : field x = (-(κ : ℂ)) ^ t.numNodes * (Y⁻¹ : ℂ) ^ (2 * t.numNodes + 1) * flatTree hk u t Y x := by
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [show field (z : AddCircle L) = physRep L (k : ℝ) tree z from physicalToHk_rep hk tree z]
    rw [show physRep L (k : ℝ) tree z = _ from physicalTree_factor (Fact.out : 0 < L) ha hY κ u t z]
    rw [flatTree_eq_bareTree]
  rw [hfield]
  dsimp [flatTree, outer, QuantumNLS.TerraMultiRound54RootFubini.positiveMeasure]
  ring

#print axioms scalar_tree_flat
end QuantumNLS.TerraMultiRound56ScalarBridge
