import QuantumNLS.Reg014Main

/-! The small-parameter half of the REG-010 upper fractional-order estimate.
The large-parameter half is the accepted REG-014 theorem. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound74SmallY
open QuantumNLS.PhysicalTensor QuantumNLS.TranslatedCorrelation QuantumNLS.FreeLimit
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.TerraMultiRound60Kernel
open QuantumNLS.TerraMultiRound61MomentRecurrence QuantumNLS.TerraMultiRound64FreeSobolev
open QuantumNLS.Reg014Moments QuantumNLS.TerraMultiRound64FieldIdentity

variable {L : ℝ} [Fact (0 < L)]

/-- Positivity and the second moments control the regularized difference. -/
theorem difference_small (μ ν : Measure ℝ) (Y : ℝ) (hY : 0 < Y)
    (hμ : Integrable (fun t : ℝ => t ^ 2) μ)
    (hν : Integrable (fun t : ℝ => t ^ 2) ν) :
    |(∫ t, kernel 2 Y t ∂μ) - ∫ t, kernel 2 Y t ∂ν| ≤
      Y ^ 2 * ((∫ t : ℝ, t ^ 2 ∂μ) + ∫ t : ℝ, t ^ 2 ∂ν) := by
  have hμk : Integrable (kernel 2 Y) μ := by
    simpa using kernel_integrable_succ μ 1 Y hY (by simpa using hμ)
  have hνk : Integrable (kernel 2 Y) ν := by
    simpa using kernel_integrable_succ ν 1 Y hY (by simpa using hν)
  have hμ0 : 0 ≤ ∫ t, kernel 2 Y t ∂μ := integral_nonneg (kernel_nonneg 2 Y)
  have hν0 : 0 ≤ ∫ t, kernel 2 Y t ∂ν := integral_nonneg (kernel_nonneg 2 Y)
  have hμle : (∫ t, kernel 2 Y t ∂μ) ≤ Y ^ 2 * ∫ t : ℝ, t ^ 2 ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono hμk (hμ.const_mul _) (fun t => by simpa using kernel_le_previous 1 Y t hY)
  have hνle : (∫ t, kernel 2 Y t ∂ν) ≤ Y ^ 2 * ∫ t : ℝ, t ^ 2 ∂ν := by
    rw [← integral_const_mul]
    exact integral_mono hνk (hν.const_mul _) (fun t => by simpa using kernel_le_previous 1 Y t hY)
  rw [abs_le]
  constructor <;> nlinarith

/-- The estimate applies to the actual physical and Fourier measures for every H¹ field. -/
theorem physical_small (κ : ℝ) (hκ : 0 < κ) (u : Hk L 1) (Y : ℝ) (hY : 0 < Y) :
    |Dfun κ hκ 2 u.val Y| ≤ Y ^ 2 *
      ((∫ t : ℝ, t ^ 2 ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) +
        ∫ t : ℝ, t ^ 2 ∂(freeMeasure L u.val)) := by
  have hu := representative_hsq (L := L) 1 u
  have hμ : Integrable (fun t : ℝ => t ^ 2)
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) := by
    simpa using physical_moment_integrable κ hκ 1 (by omega) u.val hu
  have hν : Integrable (fun t : ℝ => t ^ 2) (freeMeasure L u.val) := by
    simpa using (free_even_integrable_iff_hsq u.val 1).mpr hu
  have h := difference_small (QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)
    (freeMeasure L u.val) Y hY hμ hν
  rw [free_kernel_sum hY u.val 1 (by simpa using hν)] at h
  simpa only [Dfun, kernel, Nat.reduceMul, Nat.reduceAdd] using h

#print axioms difference_small
#print axioms physical_small
end QuantumNLS.TerraMultiRound74SmallY
