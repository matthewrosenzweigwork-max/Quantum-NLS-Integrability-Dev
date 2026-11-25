import QuantumNLS.TerraMultiRound64AllMoments
import QuantumNLS.TerraMultiRound64CorrectionField
import QuantumNLS.TerraMultiRound62FreeMoments

/-! Finite moment identities with the actual lower-order polynomial on a Sobolev field. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1 QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.TerraMultiRound59REG007 QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.TerraMultiRound62FreeMoments QuantumNLS.TerraMultiRound64FreeSobolev
open QuantumNLS.TerraMultiRound64AllMoments QuantumNLS.TerraMultiRound64CorrectionField
namespace QuantumNLS.TerraMultiRound64FieldIdentity

variable {L : ℝ} [Fact (0 < L)]

theorem representative_hsq (k : ℕ) (v : Hk L k) :
    hsq L (k : ℕ) (fun n => QuantumNLS.Fourier.coeff L v.val n) ≠ ⊤ := by
  have h := hsq_toField_ne_top L (k : ℝ) (coordinates (L := L) k v)
  have hc : (fun n => QuantumNLS.Fourier.coeff L v.val n) =
      toField L (k : ℝ) (coordinates (L := L) k v) := by
    funext n
    have hv : (physicalToHk (L := L) k (coordinates (L := L) k v)).val = v.val :=
      congrArg WField.val (physical_coordinates k v)
    rw [← QuantumNLS.Fourier.fourierL2_apply, ← hv, physicalToHk_coeff]
  rw [hc]
  exact h

theorem finite_field_identity (κ : ℝ) (hκ : 0 < κ) (s : ℕ) (hs : 2 ≤ s)
    (v : Hk L (s-1))
    (hu : hsq L (s : ℕ) (fun k => QuantumNLS.Fourier.coeff L v.val k) ≠ ⊤) :
    (∫ t : ℝ, t^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v.val)) =
      (∑' n : ℤ, (QuantumNLS.RootWeightedCellsR26.momentum L n)^(2*s) *
        ‖QuantumNLS.Fourier.coeff L v.val n‖^2) + Rfield (L := L) s hs κ v := by
  obtain ⟨x, ha, hx, hid⟩ := (integer_moment_induction L κ hκ s hs).2 v.val (representative_hsq (s-1) v)
  have hv : physicalToHk (L := L) (s-1) x = v := by
    apply WField.ext
    exact (physicalToHk_val_eq_fieldMap L (s-1) ha x).trans hx
  have he := hid hu
  rw [retained_top, hv] at he
  have hf := (free_even_integrable_iff_hsq v.val s).mpr hu
  rw [free_finite_moment v.val s hf] at he
  linarith

#print axioms representative_hsq
#print axioms finite_field_identity
end QuantumNLS.TerraMultiRound64FieldIdentity
