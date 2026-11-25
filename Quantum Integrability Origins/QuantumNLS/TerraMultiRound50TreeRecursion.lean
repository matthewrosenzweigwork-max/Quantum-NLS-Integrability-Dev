import QuantumNLS.TerraMultiRound45Trees
import QuantumNLS.TerraMultiRound47ShiftIntegrable
import QuantumNLS.RiccatiClassical

/-! Exact pointwise Laplace recursion for physical ordered tree terms. This is
one step toward the finite-dimensional path integral identity. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound50TreeRecursion
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiClassical QuantumNLS.RiccatiChargeIdent
open QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.TerraMultiRound45Trees
open QuantumNLS.TerraMultiRound47PhysicalShift

variable {L a Y : ℝ} [Fact (0 < L)]

theorem tree_leaf_laplace (hL : 0 < L) (ha : 1 / 2 < a) (hY : 0 < |Y|)
    (κ : ℝ) (u : Ell2) (x : ℝ) :
    physRep L a (treeTerm hL ha hY κ u .nil) x = (Y⁻¹ : ℂ) *
      ∫ v : ℝ in Ioi 0, (Real.exp (-v) : ℂ) * physRep L a u (x - v / Y) := by
  exact physical_resolvent_laplace L ha hY u x

/-- The two square-root factors are the physical normalization of the two
Fourier convolutions; together with κ/L they give precisely κ. -/
theorem tree_node_laplace (hL : 0 < L) (ha : 1 / 2 < a) (hY : 0 < |Y|)
    (κ : ℝ) (u : Ell2) (left right : BinaryTree Unit) (x : ℝ) :
    physRep L a (treeTerm hL ha hY κ u (.node () left right)) x =
      -(κ : ℂ) * (Y⁻¹ : ℂ) * ∫ v : ℝ in Ioi 0,
        (Real.exp (-v) : ℂ) * (starRingEnd ℂ (physRep L a u (x - v / Y)) *
          physRep L a (treeTerm hL ha hY κ u left) (x - v / Y) *
          physRep L a (treeTerm hL ha hY κ u right) (x - v / Y)) := by
  let w := mulBil hL ha (jEll u) (mulBil hL ha
    (treeTerm hL ha hY κ u left) (treeTerm hL ha hY κ u right))
  have hp : ∀ t : ℝ, physRep L a w t = (L : ℂ) *
      (starRingEnd ℂ (physRep L a u t) *
        physRep L a (treeTerm hL ha hY κ u left) t *
        physRep L a (treeTerm hL ha hY κ u right) t) := by
    intro t
    simp only [w, mulBil_apply, physRep_mulEll hL ha, physRep_jEll]
    rw [← sqrt_sq_cast hL]
    ring
  have hi : (∫ v : ℝ in Ioi 0, (Real.exp (-v) : ℂ) * physRep L a w (x - v / Y)) =
      (L : ℂ) * ∫ v : ℝ in Ioi 0, (Real.exp (-v) : ℂ) *
        (starRingEnd ℂ (physRep L a u (x - v / Y)) *
          physRep L a (treeTerm hL ha hY κ u left) (x - v / Y) *
          physRep L a (treeTerm hL ha hY κ u right) (x - v / Y)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with v
    rw [hp]
    ring
  change physRep L a (-((κ / L : ℂ) • signedCLM L Y hY w)) x = _
  rw [← neg_one_smul ℂ (((κ / L : ℂ) • signedCLM L Y hY w)),
    physRep_smul_apply, physRep_smul_apply, physical_resolvent_laplace L ha hY w x, hi]
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  push_cast
  field_simp
  <;> ring

#print axioms tree_leaf_laplace
#print axioms tree_node_laplace
end QuantumNLS.TerraMultiRound50TreeRecursion
