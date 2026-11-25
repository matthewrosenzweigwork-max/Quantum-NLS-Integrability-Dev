import QuantumNLS.TerraMultiRound64BaseCoefficient

/-! The H¹ energy identity in the common Fourier and correction notation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound59RCompatibility QuantumNLS.TerraMultiRound64BaseCoefficient
open QuantumNLS.TerraMultiRound62FreeMoments
namespace QuantumNLS.TerraMultiRound64FirstIdentity
variable {L : ℝ} [Fact (0 < L)]

theorem first_field_identity (κ : ℝ) (hκ : 0 < κ) (v : Hk L 1) :
    (∫ t : ℝ, t^2 ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v.val)) =
      (∑' n : ℤ, (QuantumNLS.RootWeightedCellsR26.momentum L n)^2 *
        ‖QuantumNLS.Fourier.coeff L v.val n‖^2) + R1field (L := L) κ v := by
  have hH := representative_oneH1 v.val v rfl
  have hf := free_second_integrable v.val hH
  have hc := first_moment_correction hκ v.val v rfl
  have hm := free_finite_moment v.val 1 hf
  simp only [mul_one] at hc hm
  rw [hm] at hc
  linarith

#print axioms first_field_identity
end QuantumNLS.TerraMultiRound64FirstIdentity
