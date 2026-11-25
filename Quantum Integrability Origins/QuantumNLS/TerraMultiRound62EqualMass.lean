import QuantumNLS.TerraMultiRound61PhysicalFree
import QuantumNLS.TerraMultiRound62Cancellation

/-! The zeroth lower-moment correction vanishes for the actual measures. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound62EqualMass
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit
variable {L κ : ℝ} [Fact (0 < L)]

theorem physical_free_mass (hκ : 0 < κ) (u : L2T L) :
    (∫ t : ℝ, t^(2*0) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
      (∫ t : ℝ, t^(2*0) ∂(freeMeasure L u)) = 0 := by
  simp only [mul_zero, pow_zero, integral_const, measureReal_def, smul_eq_mul, mul_one]
  rw [QuantumNLS.PhysicalQuantumMeasure.measure_univ, ← QuantumNLS.FullMass.Mmeas_zero_coupling,
    QuantumNLS.FullMass.Mmeas_univ]
  ring

#print axioms physical_free_mass
end QuantumNLS.TerraMultiRound62EqualMass
