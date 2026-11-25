import QuantumNLS.TerraMultiRound59OrderCompatibility
import QuantumNLS.TerraMultiRound59SobolevCoordinates
import QuantumNLS.TerraMultiRound55TreeFactors
import QuantumNLS.TerraMultiRound57CollectedPowers

/-! Tree coefficients respect equality of the underlying Sobolev fields across orders. -/
set_option autoImplicit false
noncomputable section
open ComplexConjugate
namespace QuantumNLS.TerraMultiRound59FieldOrder
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.Sobolev
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound57LevelPowers QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.TerraMultiRound59OrderCompatibility QuantumNLS.TerraMultiRound59SobolevCoordinates

variable {L : ℝ} [Fact (0 < L)]

theorem conjugate_field_order {k l : ℕ} (x y : Ell2)
    (h : (physicalToHk (L := L) k x).val = (physicalToHk (L := L) l y).val) :
    (physicalToHk (L := L) k (jEll x)).val = (physicalToHk (L := L) l (jEll y)).val := by
  apply (QuantumNLS.Fourier.fourierL2 L).injective
  ext n
  rw [physicalToHk_coeff, physicalToHk_coeff, toField_jEll, toField_jEll]
  congr 1
  have hn := congrArg (fun z => QuantumNLS.Fourier.fourierL2 L z (-n)) h
  simpa only [physicalToHk_coeff] using hn

theorem factor_field_order {k l : ℕ} (x y : Ell2) (t : BinaryTree Unit)
    (h : (physicalToHk (L := L) k x).val = (physicalToHk (L := L) l y).val) :
    ∀ i, (factorField (L := L) k x t i).val = (factorField (L := L) l y t i).val := by
  intro i
  have hj := conjugate_field_order x y h
  unfold factorField vertexField
  cases hi : finSuccEquiv (2 * t.numNodes + 1) i with
  | none => simpa only using hj
  | some j =>
    by_cases hc : internalAt t (indexedVertex t j) = true <;> simp [hc, h, hj]

theorem level_coeff_order {k l : ℕ} (κ : ℝ) (x y : Ell2) (ell d : ℕ)
    (h : (physicalToHk (L := L) k x).val = (physicalToHk (L := L) l y).val) :
    levelCoeff (L := L) (k := k) κ x ell d = levelCoeff (L := L) (k := l) κ y ell d := by
  unfold levelCoeff
  apply Finset.sum_congr rfl
  intro t ht
  rw [integrated_order_compatible _ _ _ (factor_field_order x y t h)]

theorem tree_coeff_order {k l : ℕ} (κ : ℝ) (x y : Ell2) (s n : ℕ)
    (h : (physicalToHk (L := L) k x).val = (physicalToHk (L := L) l y).val) :
    treeCoefficient (L := L) (k := k) κ x s n = treeCoefficient (L := L) (k := l) κ y s n := by
  unfold treeCoefficient
  apply Finset.sum_congr rfl
  intro ell hell
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs
  · exact level_coeff_order κ x y ell d h
  · rfl

#print axioms conjugate_field_order
#print axioms factor_field_order
#print axioms level_coeff_order
#print axioms tree_coeff_order
end QuantumNLS.TerraMultiRound59FieldOrder
