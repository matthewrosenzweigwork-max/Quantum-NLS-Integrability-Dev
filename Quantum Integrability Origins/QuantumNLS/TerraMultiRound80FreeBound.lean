import QuantumNLS.TerraMultiRound80BoundReduction

/-! A quantitative free-moment estimate at the same Sobolev order. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound77FreeContinuity
namespace QuantumNLS.TerraMultiRound80FreeBound
variable {L : ℝ} [Fact (0 < L)]

theorem free_power_le_sobolev_norm (s : ℝ) (hs : 0 ≤ s) (u : H02 L s) :
    (∫ x : ℝ, |x|^(2*s) ∂freeMeasure L u.val) ≤ ‖u‖^2 := by
  rw [free_power_eq_series s hs u, WField.norm_sq_eq_tsum]
  apply Summable.tsum_le_tsum _ (power_series_summable s hs u) u.summable
  intro n
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  change |QuantumNLS.Fourier.freq L n|^(2*s) ≤ (1+|QuantumNLS.Fourier.freq L n|)^(2*s)
  exact Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (QuantumNLS.Fourier.freq L n)]) (by positivity)

#print axioms free_power_le_sobolev_norm
end QuantumNLS.TerraMultiRound80FreeBound
