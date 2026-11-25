import QuantumNLS.TerraMultiRound66WeakFirst

/-! Norm control of the first weak derivative by the H¹ norm. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.TranslatedCorrelation QuantumNLS.WeakDerivatives QuantumNLS.Fourier
open QuantumNLS.Sobolev
namespace QuantumNLS.TerraMultiRound66WeakBound

theorem weak_derivative_norm_le (L : ℝ) [Fact (0 < L)] (u : Hk L 1)
    (g : Lp ℂ 2 (volume : Measure (AddCircle L))) (hg : HasWeakDeriv u.val g) :
    ‖g‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [← (fourierL2 L).norm_map g, QuantumNLS.Energy.norm_sq_eq_tsum, WField.norm_sq_eq_tsum]
  refine Summable.tsum_le_tsum (fun n => ?_) (QuantumNLS.Energy.summable_sq _) u.summable
  rw [fourierL2_apply, coeff_of_hasWeakDeriv hg, norm_ikn_mul_sq, fourierL2_apply]
  simp only [def002, Nat.cast_one]
  change freq L n ^ 2 * ‖coeff L u.val n‖ ^ 2 ≤ sobolevWeight L 1 n * ‖coeff L u.val n‖ ^ 2
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [sobolevWeight, mul_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  change freq L n ^ 2 ≤ (1 + |freq L n|)^2
  nlinarith [sq_abs (freq L n), abs_nonneg (freq L n)]

#print axioms weak_derivative_norm_le
end QuantumNLS.TerraMultiRound66WeakBound
