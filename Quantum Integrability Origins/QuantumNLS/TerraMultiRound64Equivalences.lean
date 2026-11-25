import QuantumNLS.TerraMultiRound64AllMoments
import QuantumNLS.TerraMultiRound64BaseCriterion
import QuantumNLS.TerraMultiRound60IndexedMoment

/-! The three printed finiteness criteria for every positive integer order. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevE1
open QuantumNLS.TerraMultiRound60IndexedMoment QuantumNLS.TerraMultiRound64BaseCriterion
open QuantumNLS.TerraMultiRound64AllMoments
namespace QuantumNLS.TerraMultiRound64Equivalences

theorem nonnegative_summable_iff_tsum_ne_top (f : ℤ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    Summable f ↔ (∑' n, ENNReal.ofReal (f n)) ≠ ⊤ := by
  constructor
  · exact fun h => h.tsum_ofReal_ne_top
  · intro h
    have hh := ENNReal.summable_toReal (f := fun n => ENNReal.ofReal (f n)) h
    simpa only [ENNReal.toReal_ofReal (hf _)] using hh

theorem integer_even_equivalences (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ)
    (s : ℕ) (hs : 1 ≤ s) (u : L2T L) :
    (hsq L (s : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ ↔
      (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*s)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ≠ ⊤) ∧
    ((∫⁻ t : ℝ, ENNReal.ofReal (t^(2*s)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ≠ ⊤ ↔
      (∑' n : ℤ, ENNReal.ofReal (‖QuantumNLS.RootWeightedCellsR26.momentum L n‖^(2*s) *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) ≠ ⊤) := by
  have hphys : Integrable (fun t : ℝ => t^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
      hsq L (s : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ := by
    by_cases h1 : s = 1
    · subst s
      simpa only [mul_one] using physical_second_iff_hsq L κ hκ u
    · exact (integer_moment_induction L κ hκ s (by omega)).1 u
  have hmeasure := lintegral_ofReal_ne_top_iff_integrable
    (μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ u)
    (by fun_prop : Continuous (fun t : ℝ => t^(2*s))).aestronglyMeasurable
    (ae_of_all _ ((even_two_mul s).pow_nonneg))
  have hi := indexed_moment_equivalence hκ u (2*s) (by omega)
  have ht : (fun t : ℝ => ‖t‖^(2*s)) = (fun t : ℝ => t^(2*s)) := by
    funext t
    simp only [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg ((even_two_mul s).pow_nonneg t)]
  rw [ht] at hi
  have hsum := nonnegative_summable_iff_tsum_ne_top
    (fun n : ℤ => ‖QuantumNLS.RootWeightedCellsR26.momentum L n‖^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) (fun n => mul_nonneg (pow_nonneg (norm_nonneg _) _)
        ((QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.1 n))
  exact ⟨hphys.symm.trans hmeasure.symm, hmeasure.trans (hi.trans hsum)⟩

#print axioms nonnegative_summable_iff_tsum_ne_top
#print axioms integer_even_equivalences
end QuantumNLS.TerraMultiRound64Equivalences
