import QuantumNLS.TerraMultiRound64FieldIdentity

/-! Extended moments retain infinity without subtracting infinite quantities. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound59RCompatibility QuantumNLS.TerraMultiRound64FieldIdentity
open QuantumNLS.TerraMultiRound64FreeSobolev QuantumNLS.TerraMultiRound64AllMoments
namespace QuantumNLS.TerraMultiRound64ExtendedIdentity

variable {L : ℝ} [Fact (0 < L)]

def extendedEvenMoment (μ : Measure ℝ) (s : ℕ) : WithTop ℝ := by
  classical
  exact if Integrable (fun t : ℝ => t^(2*s)) μ then ↑(∫ t : ℝ, t^(2*s) ∂μ) else ⊤

def extendedFourierMoment (u : L2T L) (s : ℕ) : WithTop ℝ := by
  classical
  exact if Summable (fun n : ℤ => (QuantumNLS.RootWeightedCellsR26.momentum L n)^(2*s) *
      ‖QuantumNLS.Fourier.coeff L u n‖^2) then
    ↑(∑' n : ℤ, (QuantumNLS.RootWeightedCellsR26.momentum L n)^(2*s) *
      ‖QuantumNLS.Fourier.coeff L u n‖^2) else ⊤

theorem free_integrable_iff_fourier_summable (u : L2T L) (s : ℕ) :
    Integrable (fun t : ℝ => t^(2*s)) (freeMeasure L u) ↔
      Summable (fun n : ℤ => (QuantumNLS.RootWeightedCellsR26.momentum L n)^(2*s) *
        ‖QuantumNLS.Fourier.coeff L u n‖^2) := by
  have h := free_even_integrable_iff_summable u s
  apply h.trans
  have he : (fun n : ℤ => |QuantumNLS.Fourier.freq L n|^(2*s) *
      ‖QuantumNLS.Fourier.fourierL2 L u n‖^2) =
      (fun n : ℤ => (QuantumNLS.RootWeightedCellsR26.momentum L n)^(2*s) *
        ‖QuantumNLS.Fourier.coeff L u n‖^2) := by
    funext n
    rw [← abs_pow, abs_of_nonneg ((even_two_mul s).pow_nonneg _), QuantumNLS.Fourier.fourierL2_apply]
    rfl
  rw [he]

theorem extended_field_identity (κ : ℝ) (hκ : 0 < κ) (s : ℕ) (hs : 2 ≤ s)
    (v : Hk L (s-1)) :
    extendedEvenMoment (QuantumNLS.PhysicalQuantumMeasure.measure hκ v.val) s =
      extendedFourierMoment v.val s + ↑(Rfield (L := L) s hs κ v) := by
  classical
  have hphys := (integer_moment_induction L κ hκ s hs).1 v.val
  have hfree := free_even_integrable_iff_hsq v.val s
  have hseries := free_integrable_iff_fourier_summable v.val s
  by_cases hf : Integrable (fun t : ℝ => t^(2*s)) (freeMeasure L v.val)
  · have hu := hfree.mp hf
    have hp := hphys.mpr hu
    have hsumm := hseries.mp hf
    have hid := finite_field_identity κ hκ s hs v hu
    simp only [extendedEvenMoment, extendedFourierMoment, if_pos hp, if_pos hsumm]
    exact_mod_cast hid
  · have hp : ¬ Integrable (fun t : ℝ => t^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ v.val) := by
      intro hp
      exact hf (hfree.mpr (hphys.mp hp))
    have hsum : ¬ Summable (fun n : ℤ => (QuantumNLS.RootWeightedCellsR26.momentum L n)^(2*s) *
        ‖QuantumNLS.Fourier.coeff L v.val n‖^2) := fun h => hf (hseries.mpr h)
    simp [extendedEvenMoment, extendedFourierMoment, hp, hsum]

#print axioms free_integrable_iff_fourier_summable
#print axioms extended_field_identity
end QuantumNLS.TerraMultiRound64ExtendedIdentity
