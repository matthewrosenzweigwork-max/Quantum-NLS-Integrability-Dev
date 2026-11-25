import QuantumNLS.TerraMultiRound61AllFields
import QuantumNLS.TerraMultiRound61FreeScalar
import QuantumNLS.TerraMultiRound60Kernel

/-! Zeroth regularizations of the physical and free measures. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound61InitialBridge
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RootH1RatioBounds
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound61AllFields
open QuantumNLS.TerraMultiRound60Kernel
variable {L : ℝ} [Fact (0 < L)]

theorem physical_regularized_zero {a Y κ : ℝ} (ha : 1 / 2 < a) (hY : 0 < Y)
    (hlog : Real.log 3 ≤ Y * L) (hκ : 0 < κ) (u : L2T L)
    (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y) (x r : Ell2)
    (hx : fieldMap L a (by linarith) x = u)
    (hr : fieldMap L a (by linarith) r = ratioL2 hY hlog hκ.le u hsmall) :
    (∫ t, kernel 0 Y t ∂(PhysicalQuantumMeasure.measure hκ u)) = Y * (scalar L a x r).re := by
  rw [scalar_real_poisson_all ha hY hlog hκ u hsmall x r hx hr, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  unfold kernel QuantumNLS.CauchyUniqueness.pk
  simp only [mul_zero, pow_zero, mul_one, neg_sq]
  ring

#print axioms physical_regularized_zero
end QuantumNLS.TerraMultiRound61InitialBridge
