import QuantumNLS.TerraMultiRound64ExtendedMeasure
import QuantumNLS.TerraMultiRound62FreeMoments

/-! The extended Fourier expression agrees with the nonnegative extended series. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound62FreeMoments QuantumNLS.TerraMultiRound64ExtendedIdentity
open QuantumNLS.TerraMultiRound64ExtendedMeasure
namespace QuantumNLS.TerraMultiRound64ExtendedFourier
variable {L : ℝ} [Fact (0 < L)]

theorem extended_fourier_eq_free (u : L2T L) (s : ℕ) :
    extendedFourierMoment u s = extendedEvenMoment (freeMeasure L u) s := by
  classical
  have hi := free_integrable_iff_fourier_summable u s
  by_cases hf : Integrable (fun t : ℝ => t^(2*s)) (freeMeasure L u)
  · have hs := hi.mp hf
    have h := free_finite_moment u s hf
    simp only [extendedFourierMoment, extendedEvenMoment, if_pos hs, if_pos hf]
    rw [h]
  · have hs : ¬ Summable (fun n : ℤ => (QuantumNLS.RootWeightedCellsR26.momentum L n)^(2*s) *
        ‖QuantumNLS.Fourier.coeff L u n‖^2) := fun hs => hf (hi.mpr hs)
    simp [extendedFourierMoment, extendedEvenMoment, hs, hf]

theorem extended_fourier_eq_series (u : L2T L) (s : ℕ) :
    extendedFourierMoment u s = ennrealToWithTop
      (∑' n : ℤ, ENNReal.ofReal ((QuantumNLS.RootWeightedCellsR26.momentum L n)^(2*s) *
        ‖QuantumNLS.Fourier.coeff L u n‖^2)) := by
  rw [extended_fourier_eq_free, extended_moment_eq_lintegral, free_extended_moment]
  congr 1
  apply tsum_congr
  intro n
  rw [ENNReal.ofReal_mul ((even_two_mul s).pow_nonneg _)]
  ring

#print axioms extended_fourier_eq_free
#print axioms extended_fourier_eq_series
end QuantumNLS.TerraMultiRound64ExtendedFourier
