import QuantumNLS.TerraMultiRound61InitialBridge
import QuantumNLS.TerraMultiRound61FreeMeasure

/-! Exact physical/free scalar difference as a difference of finite kernels. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound61PhysicalFree
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RootH1RatioBounds
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound57Collection
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound61InitialBridge
open QuantumNLS.TerraMultiRound61FreeMeasure QuantumNLS.FreeLimit
variable {L : ℝ} [Fact (0 < L)]

theorem regularized_scalar_difference {a Y κ : ℝ} (ha : 1 / 2 < a) (hY : 0 < Y)
    (hlog : Real.log 3 ≤ Y * L) (hκ : 0 < κ) (u : L2T L)
    (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y) (x r : Ell2)
    (hx : fieldMap L a (by linarith) x = u)
    (hr : fieldMap L a (by linarith) r = ratioL2 hY hlog hκ.le u hsmall) :
    (∫ t, kernel 0 Y t ∂(PhysicalQuantumMeasure.measure hκ u)) -
      (∫ t, kernel 0 Y t ∂(freeMeasure L u)) =
      Y * (scalar L a x r - freeScalar (L := L) a x Y).re := by
  have hf := free_scalar_measure (L := L) ha hY x
  rw [hx] at hf
  rw [physical_regularized_zero ha hY hlog hκ u hsmall x r hx hr, hf, Complex.sub_re]
  ring

#print axioms regularized_scalar_difference
end QuantumNLS.TerraMultiRound61PhysicalFree
