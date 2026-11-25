import QuantumNLS.TerraMultiRound66WeakSecond
import QuantumNLS.TerraMultiRound66WeakMap
import QuantumNLS.TerraMultiRound64Equivalences
import QuantumNLS.TerraMultiRound64FreeSobolev

/-! Extended free fourth moment and the second weak derivative. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Fourier QuantumNLS.WeakDerivatives
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.TranslatedCorrelation
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.TerraMultiRound66WeakMap
open QuantumNLS.TerraMultiRound66WeakSecond QuantumNLS.TerraMultiRound64Equivalences
open QuantumNLS.TerraMultiRound64FreeSobolev
namespace QuantumNLS.TerraMultiRound67ExtendedSecond
variable {L : ℝ} [Fact (0 < L)]

def freeFourth (u : Hk L 1) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal ((momentum L n)^4 * ‖coeff L u.val n‖^2)

theorem second_exists_iff_summable (u : Hk L 1) :
    (∃ w, HasWeakDeriv (weakD u) w) ↔
    Summable (fun n : ℤ => (momentum L n)^4 * ‖coeff L u.val n‖^2) := by
  rw [exists_hasWeakDeriv_iff]
  apply summable_congr
  intro n
  rw [coeff_of_hasWeakDeriv (weakD_is_derivative u), norm_ikn_mul_sq]
  change Fourier.freq L n ^ 2 * (Fourier.freq L n ^ 2 * ‖coeff L u.val n‖ ^ 2) = _
  rw [show momentum L n = Fourier.freq L n from rfl]
  ring

theorem second_exists_iff_freeFourth_finite (u : Hk L 1) :
    (∃ w, HasWeakDeriv (weakD u) w) ↔ freeFourth u ≠ ⊤ := by
  rw [second_exists_iff_summable]
  exact nonnegative_summable_iff_tsum_ne_top _ (fun n => by positivity)

theorem freeFourth_eq_norm (u : Hk L 1) {w : L2T L}
    (hw : HasWeakDeriv (weakD u) w) : freeFourth u = ENNReal.ofReal (‖w‖^2) := by
  have hs := (second_exists_iff_summable u).1 ⟨w, hw⟩
  rw [freeFourth, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs,
    fourth_fourier_eq_weak_second_norm L (weakD_is_derivative u) hw]

theorem freeFourth_eq_top (u : Hk L 1) (h : ¬ ∃ w, HasWeakDeriv (weakD u) w) :
    freeFourth u = ⊤ := by
  by_contra hn
  exact h ((second_exists_iff_freeFourth_finite u).2 hn)

theorem second_exists_iff_H2 (u : Hk L 1) :
    (∃ w, HasWeakDeriv (weakD u) w) ↔
      hsq L 2 (fun n => coeff L u.val n) ≠ ⊤ := by
  rw [second_exists_iff_summable]
  have h := (free_even_integrable_iff_summable u.val 2).symm.trans
    (free_even_integrable_iff_hsq u.val 2)
  have habs (x : ℝ) : |x|^4 = x^4 := by nlinarith [sq_abs x, sq_nonneg (x^2)]
  simpa only [show 2 * 2 = 4 by norm_num, momentum, ← fourierL2_apply,
    habs, Fourier.freq, Nat.cast_ofNat] using h

#print axioms second_exists_iff_summable
#print axioms second_exists_iff_freeFourth_finite
#print axioms freeFourth_eq_norm
#print axioms freeFourth_eq_top
#print axioms second_exists_iff_H2
end QuantumNLS.TerraMultiRound67ExtendedSecond
