import QuantumNLS.TerraMultiRound76ExtendedKernel
import QuantumNLS.TerraMultiRound74SmallY

/-! Specialization of the extended positive kernels to the actual physical
and free measures. No subtraction of infinite moments is used. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound76ExtendedKernel
namespace QuantumNLS.TerraMultiRound76PhysicalKernels

variable {L : ℝ} [Fact (0 < L)]

theorem physical_free_low_kernels (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    let C := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1
    let μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ u
    let ν := freeMeasure L u
    ENNReal.ofReal C * (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2*s)) ∂μ) =
      (∫⁻ t in Ioi 0, ∫⁻ x : ℝ, ENNReal.ofReal (Real.rpowIntegrand₀₁ s t (x^2)) ∂μ) ∧
    ENNReal.ofReal C * (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2*s)) ∂ν) =
      (∫⁻ t in Ioi 0, ∫⁻ x : ℝ, ENNReal.ofReal (Real.rpowIntegrand₀₁ s t (x^2)) ∂ν) := by
  haveI : IsFiniteMeasure (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
    rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas]
    infer_instance
  haveI : IsFiniteMeasure (freeMeasure L u) := by
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    infer_instance
  exact ⟨low_extended_moment _ s hs0 hs1, low_extended_moment _ s hs0 hs1⟩

theorem physical_free_upper_kernels (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2) :
    let C := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1
    let μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ u
    let ν := freeMeasure L u
    ENNReal.ofReal C * (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2*s)) ∂μ) =
      (∫⁻ t in Ioi 0, ∫⁻ x : ℝ, ENNReal.ofReal (x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2)) ∂μ) ∧
    ENNReal.ofReal C * (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2*s)) ∂ν) =
      (∫⁻ t in Ioi 0, ∫⁻ x : ℝ, ENNReal.ofReal (x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2)) ∂ν) := by
  haveI : IsFiniteMeasure (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
    rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas]
    infer_instance
  haveI : IsFiniteMeasure (freeMeasure L u) := by
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    infer_instance
  exact ⟨upper_extended_moment _ s hs1 hs2, upper_extended_moment _ s hs1 hs2⟩

/-- The free extended power moment is exactly the Fourier series, including
when it is infinite. -/
theorem free_fourier_power_moment (u : L2T L) (p : ℝ) :
    (∫⁻ t : ℝ, ENNReal.ofReal (|t| ^ p) ∂(freeMeasure L u)) =
      ∑' n : ℤ, ENNReal.ofReal (‖QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n‖ ^ 2) *
        ENNReal.ofReal (|QuantumNLS.RootWeightedCellsR26.momentum L n| ^ p) := by
  unfold freeMeasure
  rw [lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl

#print axioms free_fourier_power_moment
#print axioms physical_free_low_kernels
#print axioms physical_free_upper_kernels
end QuantumNLS.TerraMultiRound76PhysicalKernels
