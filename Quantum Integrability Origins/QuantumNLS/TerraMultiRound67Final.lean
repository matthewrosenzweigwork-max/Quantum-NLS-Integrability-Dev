import QuantumNLS.TerraMultiRound67REG008

/-! The REG-008 theorem with the printed correction explicitly equated to the
    continuous real polynomial in the same statement. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.TranslatedCorrelation QuantumNLS.WeakDerivatives QuantumNLS.RiccatiSobolevE1
open QuantumNLS.TerraMultiRound59PolynomialProperty QuantumNLS.TerraMultiRound64ExtendedMeasure
open QuantumNLS.TerraMultiRound66WeakMap QuantumNLS.TerraMultiRound67ExtendedIdentity
open QuantumNLS.TerraMultiRound67DensityCandidate QuantumNLS.TerraMultiRound67DensityExtension
open QuantumNLS.TerraMultiRound67Correction QuantumNLS.TerraMultiRound67REG008
namespace QuantumNLS.TerraMultiRound67Final

/-- The printed REG-008 clauses, including the explicit correction as the
    same continuous real polynomial, in one named theorem. -/
theorem REG008_complete (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) :
    (∀ u : Hk L 1,
      correction κ u = κ * (∫ x : AddCircle L,
        6 * (‖contRep (by omega) u x‖^2 * ‖(weakD u : AddCircle L → ℂ) x‖^2) +
        ‖(densityCandidate u : AddCircle L → ℂ) x‖^2 ∂volume) +
        2 * κ^2 * ∫ x : AddCircle L, ‖contRep (by omega) u x‖^6 ∂volume) ∧
    RealPolynomial (correction (L := L) κ) ∧ Continuous (correction (L := L) κ) ∧
    (∀ u : Hk L 1,
      HasWeakDeriv u.val (weakD u) ∧
      ((densityClass u : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))]
        fun x => ((‖contRep (by omega) u x‖^2 : ℝ) : ℂ)) ∧
      HasWeakDeriv (densityClass u) (densityCandidate u) ∧
      ennrealToWithTop (∫⁻ t : ℝ, ENNReal.ofReal (t^4)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) =
      ennrealToWithTop (secondExtended u) + ↑((κ * (∫ x : AddCircle L,
        6 * (‖contRep (by omega) u x‖^2 * ‖(weakD u : AddCircle L → ℂ) x‖^2) +
        ‖(densityCandidate u : AddCircle L → ℂ) x‖^2 ∂volume) +
        2 * κ^2 * ∫ x : AddCircle L, ‖contRep (by omega) u x‖^6 ∂volume : ℝ))) ∧
    (∀ u : Hk L 1,
      (∫⁻ t : ℝ, ENNReal.ofReal (t^4)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) ≠ ⊤ ↔
      hsq L 2 (fun n => QuantumNLS.Fourier.coeff L u.val n) ≠ ⊤) ∧
    (∀ (u : Hk L 1) (w : QuantumNLS.PhysicalTensor.L2T L),
      HasWeakDeriv (weakD u) w → secondExtended u = ENNReal.ofReal (‖w‖^2)) ∧
    (∀ u : Hk L 1, (¬ ∃ w, HasWeakDeriv (weakD u) w) → secondExtended u = ⊤) := by
  exact ⟨correction_printed κ, REG008 L κ hκ⟩

#print axioms REG008_complete
end QuantumNLS.TerraMultiRound67Final
