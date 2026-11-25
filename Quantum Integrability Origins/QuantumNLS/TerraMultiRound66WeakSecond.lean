import QuantumNLS.TerraMultiRound65FourthCore
import QuantumNLS.WeakDerivatives

/-! Identification of the finite free fourth moment with the L² second weak derivative. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.Fourier QuantumNLS.WeakDerivatives
open QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound66WeakSecond

theorem fourth_fourier_eq_weak_second_norm (L : ℝ) [Fact (0 < L)]
    {u v w : L2T L} (h₁ : HasWeakDeriv u v) (h₂ : HasWeakDeriv v w) :
    (∑' n : ℤ, (momentum L n)^4 * ‖coeff L u n‖^2) = ‖w‖^2 := by
  rw [← (fourierL2 L).norm_map w, QuantumNLS.Energy.norm_sq_eq_tsum]
  congr 1
  funext n
  rw [fourierL2_apply, coeff_of_hasWeakDeriv h₂ n, norm_ikn_mul_sq,
    coeff_of_hasWeakDeriv h₁ n, norm_ikn_mul_sq]
  have hm : momentum L n = freq L n := rfl
  rw [hm]
  ring

#print axioms fourth_fourier_eq_weak_second_norm
end QuantumNLS.TerraMultiRound66WeakSecond
