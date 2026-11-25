import QuantumNLS.TerraMultiRound64FourthCharacterization
import QuantumNLS.RiccatiSobolevS

/-! Fourth-moment finiteness characterizes H² for arbitrary L² fields. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevS
open QuantumNLS.FreeLimit QuantumNLS.TerraMultiRound60IndexedMoment
open QuantumNLS.TerraMultiRound64BaseCoefficient QuantumNLS.TerraMultiRound64FreeSobolev
open QuantumNLS.TerraMultiRound64FourthCharacterization
namespace QuantumNLS.TerraMultiRound64FourthAllFields

theorem physical_second_of_fourth (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ)
    (u : L2T L) (h4 : Integrable (fun t : ℝ => t^4) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) :
    Integrable (fun t : ℝ => t^2) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := integrable_const _
  apply (hconst.add h4).mono'
  · exact (by fun_prop : Continuous (fun t : ℝ => t^2)).aestronglyMeasurable
  · apply ae_of_all
    intro t
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t),
      abs_of_nonneg (by positivity : 0 ≤ 1 + t^4)]
    nlinarith [sq_nonneg (t^2-1)]

theorem fourth_characterization_all_fields (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (u : L2T L) :
    (Integrable (fun t : ℝ => t^4) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
      hsq L (2 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) ∧
    (Integrable (fun t : ℝ => t^4) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => ‖QuantumNLS.RootWeightedCellsR26.momentum L n‖^4 *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) := by
  have hp : Integrable (fun t : ℝ => t^4) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) →
      hsq L (1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ := by
    intro h4
    have h2 := physical_second_of_fourth L κ hκ u h4
    rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas hκ u] at h2
    have hH := (QuantumNLS.RDF8Main.root_H1_characterization hκ u).1.mpr h2
    exact (free_even_integrable_iff_hsq u 1).mp (free_second_integrable u hH)
  have hs : hsq L (2 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ →
      hsq L (1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ := by
    intro h
    exact ne_top_of_le_ne_top h (hsq_mono (by norm_num) _)
  have heq : Integrable (fun t : ℝ => t^4) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
      hsq L (2 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ := by
    constructor
    · intro h
      obtain ⟨_, _, _, hh, _, _⟩ := fourth_characterization_on_H1 L κ hκ u (hp h)
      exact hh.mp h
    · intro h
      obtain ⟨_, _, _, hh, _, _⟩ := fourth_characterization_on_H1 L κ hκ u (hs h)
      exact hh.mpr h
  have hi := indexed_moment_equivalence hκ u 4 (by norm_num)
  have ht : (fun t : ℝ => ‖t‖^4) = (fun t : ℝ => t^4) := by
    funext t
    simp only [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ t^4)]
  rw [ht] at hi
  exact ⟨heq, hi⟩

#print axioms physical_second_of_fourth
#print axioms fourth_characterization_all_fields
end QuantumNLS.TerraMultiRound64FourthAllFields
