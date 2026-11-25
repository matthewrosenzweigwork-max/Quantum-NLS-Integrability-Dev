import QuantumNLS.TerraMultiRound59Transfer

/-! The first, quartic coefficient is compatible with higher Sobolev orders. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59QuarticTransfer
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.TerraMultiRound59CoefficientPolynomial QuantumNLS.TerraMultiRound59MinimalPolynomial
open QuantumNLS.TerraMultiRound59SobolevCoordinates QuantumNLS.TerraMultiRound59FieldOrder
open QuantumNLS.TerraMultiRound59TreeOrder QuantumNLS.TerraMultiRound59RCompatibility

variable {L : ℝ} [Fact (0 < L)]

theorem R1field_transfer (s : ℕ) (hs : 2 ≤ s) (κ : ℝ) (u : Hk L (s - 1))
    (hst : ((1 : ℕ) : ℝ) ≤ ((s - 1 : ℕ) : ℝ)) :
    R1field (L := L) κ (H02.mono (L := L) hst u) =
      -(treeCoefficient (L := L) (k := s - 1) κ
        (coordinates (L := L) (s - 1) u) s 3).re := by
  let x := coordinates (L := L) 1 (H02.mono hst u)
  let y := coordinates (L := L) (s - 1) u
  have hv : (physicalToHk (L := L) 1 x).val = (physicalToHk (L := L) (s - 1) y).val := by
    dsimp [x, y]
    rw [physical_coordinates, physical_coordinates]
    exact fieldIncl_val _ _ _ _ _
  have ho := tree_coeff_order (L := L) (k := 1) (l := s - 1) κ x y 2 3 hv
  have ht := tree_coefficient_truncation_stable (L := L) (k := s - 1) κ y 2 s 3 hs (by omega)
  change -coefficientPolynomial (L := L) (k := 1) (by omega) κ 2 3 x = _
  rw [coefficientPolynomial_eq (L := L) (k := 1) (by omega) κ 2 3 (by omega) x, ho, ht]

#print axioms R1field_transfer
end QuantumNLS.TerraMultiRound59QuarticTransfer
