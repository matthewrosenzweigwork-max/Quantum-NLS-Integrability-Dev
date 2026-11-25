import QuantumNLS.TerraMultiRound59RCompatibility

/-! Compatibility of minimal odd coefficients with a higher Sobolev realization. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59Transfer
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.TerraMultiRound59CoefficientPolynomial QuantumNLS.TerraMultiRound59MinimalPolynomial
open QuantumNLS.TerraMultiRound59SobolevCoordinates QuantumNLS.TerraMultiRound59FieldOrder
open QuantumNLS.TerraMultiRound59TreeOrder QuantumNLS.TerraMultiRound59RCompatibility

variable {L : ℝ} [Fact (0 < L)]

theorem minimal_coefficient_transfer (j s : ℕ) (hj : 2 ≤ j) (hjs : j ≤ s)
    (κ : ℝ) (x y : Ell2)
    (hv : (physicalToHk (L := L) (j - 1) x).val = (physicalToHk (L := L) (s - 1) y).val) :
    coefficientPolynomial (L := L) (k := j - 1) (by omega) κ j (2 * j + 1) x =
      (treeCoefficient (L := L) (k := s - 1) κ y s (2 * j + 1)).re := by
  rw [coefficientPolynomial_eq (L := L) (k := j - 1) (by omega) κ j (2 * j + 1) (by omega) x]
  rw [tree_coeff_order (L := L) (k := j - 1) (l := s - 1) κ x y j (2 * j + 1) hv]
  rw [tree_coefficient_truncation_stable (L := L) (k := s - 1) κ y j s (2 * j + 1) hjs le_rfl]

theorem Rfield_transfer (j s : ℕ) (hj : 2 ≤ j) (hjs : j ≤ s) (κ : ℝ)
    (u : Hk L (s - 1))
    (hst : ((j - 1 : ℕ) : ℝ) ≤ ((s - 1 : ℕ) : ℝ)) :
    Rfield (L := L) j hj κ (H02.mono (L := L) hst u) =
      (-1 : ℝ) ^ j * (treeCoefficient (L := L) (k := s - 1) κ
        (coordinates (L := L) (s - 1) u) s (2 * j + 1)).re := by
  have hv : (physicalToHk (L := L) (j - 1) (coordinates (L := L) (j - 1) (H02.mono hst u))).val =
      (physicalToHk (L := L) (s - 1) (coordinates (L := L) (s - 1) u)).val := by
    rw [physical_coordinates, physical_coordinates]
    exact fieldIncl_val _ _ _ _ _
  have hc := minimal_coefficient_transfer j s hj hjs κ _ _ hv
  change (-1 : ℝ) ^ j * coefficientPolynomial (L := L) (k := j - 1) (by omega) κ j (2 * j + 1) _ = _
  rw [hc]

#print axioms minimal_coefficient_transfer
#print axioms Rfield_transfer
end QuantumNLS.TerraMultiRound59Transfer
