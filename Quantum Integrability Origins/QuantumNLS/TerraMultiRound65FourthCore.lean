import QuantumNLS.TerraMultiRound64REG004

/-! The fourth-order specialization of REG-004, prior to identification of
its nonlinear correction with the printed derivative integrals. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevE1 QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound59RCompatibility QuantumNLS.TerraMultiRound59PolynomialProperty
open QuantumNLS.TerraMultiRound64ExtendedIdentity QuantumNLS.TerraMultiRound64ExtendedMeasure
open QuantumNLS.TerraMultiRound64REG004
namespace QuantumNLS.TerraMultiRound65FourthCore

theorem fourth_order_core (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) :
    RealPolynomial (Rfield (L := L) 2 (by omega) κ) ∧
    Continuous (Rfield (L := L) 2 (by omega) κ) ∧
    (∀ v : Hk L 1,
      ennrealToWithTop (∫⁻ t : ℝ, ENNReal.ofReal (t^4)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v.val)) =
      ennrealToWithTop (∑' n : ℤ, ENNReal.ofReal
        ((QuantumNLS.RootWeightedCellsR26.momentum L n)^4 *
          ‖QuantumNLS.Fourier.coeff L v.val n‖^2)) +
        ↑(Rfield (L := L) 2 (by omega) κ v)) ∧
    (∀ v : Hk L 1,
      (∫⁻ t : ℝ, ENNReal.ofReal (t^4)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v.val)) ≠ ⊤ ↔
      hsq L 2 (fun k => QuantumNLS.Fourier.coeff L v.val k) ≠ ⊤) := by
  have h := REG004 L κ hκ
  refine ⟨(h.2.1 2 (by omega)).1, (h.2.1 2 (by omega)).2, ?_, ?_⟩
  · intro v
    simpa using h.2.2.2.1 2 (by omega) v
  · intro v
    simpa using ((h.1 2 (by omega) v.val).1).symm

#print axioms fourth_order_core
end QuantumNLS.TerraMultiRound65FourthCore
