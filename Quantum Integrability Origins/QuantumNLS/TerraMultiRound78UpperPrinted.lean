import QuantumNLS.TerraMultiRound78UpperPhysical
import QuantumNLS.Reg010LowPrinted

/-! Literal sine coefficient in the upper finite-moment identity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.TranslatedCorrelation
open QuantumNLS.Reg010LowKernel QuantumNLS.Reg010LowCorrection QuantumNLS.Reg010LowPrinted
open QuantumNLS.TerraMultiRound78UpperPhysical QuantumNLS.TerraMultiRound75Correction
namespace QuantumNLS.TerraMultiRound78UpperPrinted

variable {L : ℝ} [Fact (0 < L)]

theorem upper_coefficient (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2) :
    2 / (∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1) = coefficient (s-1) := by
  have h0 : 0 < s-1 := by linarith
  have h1 : s-1 < 1 := by linarith
  have hp := normalization_pos (s-1) h0 h1
  have hc := coefficient_normalization (s-1) h0 h1
  have he : (∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1) = 2 * normalization (s-1) := by
    unfold normalization
    ring
  rw [he]
  apply (div_eq_iff (by positivity : 2 * normalization (s-1) ≠ 0)).2
  nlinarith

theorem physical_free_upper_printed (κ : ℝ) (hκ : 0 < κ) (u : Hk L 1)
    (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2)
    (hμ : Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u.val))
    (hν : Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L u.val)) :
    (∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ u.val) =
      (∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L u.val) +
        (2 * Real.sin (Real.pi * (s-1)) / Real.pi) * correction κ hκ s u := by
  have h := physical_free_upper_finite κ hκ u s hs1 hs2 hμ hν
  rw [upper_coefficient s hs1 hs2] at h
  have h' := sub_eq_iff_eq_add.mp h
  simpa only [coefficient, add_comm] using h'

#print axioms upper_coefficient
#print axioms physical_free_upper_printed
end QuantumNLS.TerraMultiRound78UpperPrinted
