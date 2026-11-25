import QuantumNLS.RDF8Main
import QuantumNLS.TerraMultiRound59REG007
import QuantumNLS.TerraMultiRound62FreeMoments

/-! Identify the first correction using the accepted H¹ energy identity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Sobolev
open QuantumNLS.TranslatedCorrelation QuantumNLS.ProductEnergyPreparation
open QuantumNLS.TerraMultiRound59RCompatibility QuantumNLS.TerraMultiRound59REG007
open QuantumNLS.TerraMultiRound62FreeMoments
namespace QuantumNLS.TerraMultiRound64BaseCoefficient

variable {L κ : ℝ} [Fact (0 < L)]

theorem free_second_integrable (u : L2T L) (hH : OneH1 u) :
    Integrable (fun t : ℝ => t^(2*1)) (freeMeasure L u) := by
  have hs : Summable (fun n : ℤ => QuantumNLS.Fourier.freq L n ^ 2 *
      ‖QuantumNLS.Fourier.fourierL2 L u n‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ hH
    intro n
    change _ ≤ QuantumNLS.Fourier.f04Weight L 1 n * ‖QuantumNLS.Fourier.fourierL2 L u n‖^2
    rw [QuantumNLS.Fourier.f04Weight_one]
    nlinarith [sq_nonneg ‖QuantumNLS.Fourier.fourierL2 L u n‖]
  change Integrable (fun t : ℝ => t^(2*1)) (Measure.sum (fun n : ℤ =>
    ENNReal.ofReal (‖QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n‖ ^ 2) •
      Measure.dirac (2 * Real.pi * n / L)))
  apply integrable_sum_dirac (fun n => by simp)
  convert hs using 1
  funext n
  simp only [mul_one]
  rw [ENNReal.toReal_ofReal (sq_nonneg _), Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [QuantumNLS.Fourier.fourierL2_apply]
  simp only [QuantumNLS.Fourier.freq, mul_one]
  ring

theorem representative_oneH1 (u : L2T L) (v : Hk L 1) (hv : v.val = u) : OneH1 u := by
  change QuantumNLS.Fourier.Mem04 L 1 (fun n => QuantumNLS.Fourier.fourierL2 L u n)
  rw [← hv, ← toF1_val (by omega) v]
  exact (toF1 (by omega) v).summable

theorem first_moment_correction (hκ : 0 < κ) (u : L2T L) (v : Hk L 1)
    (hv : v.val = u) :
    (∫ t : ℝ, t^(2*1) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
      (∫ t : ℝ, t^(2*1) ∂(freeMeasure L u)) = R1field (L := L) κ v := by
  have hH := representative_oneH1 u v hv
  have hp := ((QuantumNLS.RDF8Main.root_H1_characterization hκ u).2.2.1 hH).1
  rw [← QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas hκ u] at hp
  have hf := free_finite_moment u 1 (free_second_integrable u hH)
  have hq : QuantumNLS.ChargeEnergy.quartic (u : AddCircle L → ℂ) =
      ∫ y : AddCircle L, ‖contRep (by omega) v y‖ ^ 4 ∂(volume : Measure (AddCircle L)) := by
    unfold QuantumNLS.ChargeEnergy.quartic
    apply integral_congr_ae
    have he := ae_eq_contRep (by omega) v
    rw [hv] at he
    filter_upwards [he] with y hy
    rw [hy]
  rw [R1field_quartic, hp, hf]
  unfold QuantumNLS.ChargeEnergy.energyH1 QuantumNLS.ChargeEnergy.kinetic
  rw [hq]
  simp only [QuantumNLS.Fourier.freq, QuantumNLS.RootWeightedCellsR26.momentum]
  ring

#print axioms representative_oneH1
#print axioms free_second_integrable
#print axioms first_moment_correction
end QuantumNLS.TerraMultiRound64BaseCoefficient
