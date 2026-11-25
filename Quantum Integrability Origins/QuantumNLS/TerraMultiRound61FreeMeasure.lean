import QuantumNLS.TerraMultiRound61MomentRecurrence
import QuantumNLS.TerraMultiRound61FreeScalar

/-! Identify the free Fourier Poisson sum with its actual atomic measure. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound61FreeMeasure
open QuantumNLS.PhysicalTensor QuantumNLS.Fourier QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound61MomentRecurrence
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TerraMultiRound57Collection
open QuantumNLS.TerraMultiRound61FreeScalar
variable {L : ℝ} [Fact (0 < L)]

theorem free_regularized_zero {Y : ℝ} (hY : 0 < Y) (u : L2T L) :
    (∫ t, kernel 0 Y t ∂(freeMeasure L u)) =
      ∑' n : ℤ, (Y^2 / (Y^2 + momentum L n ^ 2)) * ‖fourierL2 L u n‖ ^ 2 := by
  haveI : IsFiniteMeasure (freeMeasure L u) := by
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    infer_instance
  have hm : Integrable (fun t : ℝ => t ^ (2*0)) (freeMeasure L u) := by
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (freeMeasure L u))
  have hi := kernel_integrable (freeMeasure L u) 0 Y hY hm
  change Integrable (kernel 0 Y) (Measure.sum (fun n : ℤ =>
    ENNReal.ofReal (‖coeff L (u : AddCircle L → ℂ) n‖ ^ 2) •
      Measure.dirac (2 * Real.pi * n / L))) at hi
  have hs := hasSum_integral_measure hi
  have he := hs.tsum_eq.symm
  convert he using 1
  · rfl
  · apply tsum_congr
    intro n
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
    simp only [kernel, mul_zero, pow_zero, mul_one]
    rw [fourierL2_apply]
    unfold momentum
    ring

theorem free_scalar_measure {a Y : ℝ} (ha : 1 / 2 < a) (hY : 0 < Y) (x : Ell2) :
    (∫ t, kernel 0 Y t ∂(freeMeasure L (fieldMap L a (by linarith) x))) =
      Y * (freeScalar (L := L) a x Y).re := by
  rw [free_regularized_zero hY, free_scalar_poisson ha hY]

#print axioms free_regularized_zero
#print axioms free_scalar_measure
end QuantumNLS.TerraMultiRound61FreeMeasure
