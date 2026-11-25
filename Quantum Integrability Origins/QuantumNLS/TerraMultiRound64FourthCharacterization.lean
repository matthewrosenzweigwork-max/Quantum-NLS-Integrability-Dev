import QuantumNLS.TerraMultiRound64FourthMoment
import QuantumNLS.TerraMultiRound64FreeSobolev
import QuantumNLS.TerraMultiRound60IndexedMoment

/-! The fourth-moment equivalences and finite identity for H¹ fields. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound59SignedCharges
open QuantumNLS.TerraMultiRound62FreeMoments QuantumNLS.TerraMultiRound60IndexedMoment
open QuantumNLS.TerraMultiRound64FourthMoment QuantumNLS.TerraMultiRound64FreeSobolev
namespace QuantumNLS.TerraMultiRound64FourthCharacterization

theorem fourth_characterization_on_H1 (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ)
    (u : L2T L) (hu : hsq L (1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ x : Ell2, ∃ ha0 : 0 ≤ ((1 : ℕ) : ℝ), fieldMap L (1 : ℕ) ha0 x = u ∧
      (Integrable (fun t : ℝ => t^4) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
        hsq L (2 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) ∧
      (Integrable (fun t : ℝ => t^4) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
        Summable (fun n : ℤ => ‖QuantumNLS.RootWeightedCellsR26.momentum L n‖^4 *
          (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) ∧
      (hsq L (2 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ →
        (∫ t : ℝ, t^4 ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) =
          (∑' n : ℤ, (QuantumNLS.RootWeightedCellsR26.momentum L n)^4 *
            ‖QuantumNLS.Fourier.coeff L u n‖^2) +
          retainedR (L := L) 2 (by omega) κ (physicalToHk (L := L) (2-1) x) 2) := by
  obtain ⟨x, ha0, hx, heq, hidentity⟩ := fourth_moment_transfer L κ hκ u hu
  have hf : Integrable (fun t : ℝ => t^4) (freeMeasure L u) ↔
      hsq L (2 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ := by
    simpa using free_even_integrable_iff_hsq u 2
  have hi := indexed_moment_equivalence hκ u 4 (by norm_num)
  have ht : (fun t : ℝ => ‖t‖^4) = (fun t : ℝ => t^4) := by
    funext t
    simp only [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ t^4)]
  rw [ht] at hi
  refine ⟨x, ha0, hx, heq.trans hf, hi, ?_⟩
  intro h
  have hfree := hf.mpr h
  have hm := free_finite_moment u 2 (by simpa using hfree)
  have hid := hidentity hfree
  rw [hm] at hid
  simpa using hid

#print axioms fourth_characterization_on_H1
end QuantumNLS.TerraMultiRound64FourthCharacterization
