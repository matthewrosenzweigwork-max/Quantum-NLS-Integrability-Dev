import QuantumNLS.Reg014Main
/-! integrator-authored trusted spec for REG-014 CC:all-fractional:uniform (terra_review r219 ACCEPT): headline statement(s) copied verbatim from Reg014Main (QuantumNLS.Reg014Main). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.REG014Spec
open QuantumNLS.Reg014Main
open QuantumNLS.TranslatedCorrelation QuantumNLS.Reg014Moments QuantumNLS.Reg014Continuity
open QuantumNLS.Reg014Finite

set_option maxHeartbeats 8000000 in
theorem REG014_spec (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (r : ℕ) (hr : 2 ≤ r) :
    (∀ (u : Hk L (r - 1)) (Y : ℝ), 0 < Y →
      Integrable (fun t : ℝ => Y ^ 2 * t ^ (2 * r) / (Y ^ 2 + t ^ 2))
          (QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) ∧
        Summable (fun n : ℤ => Y ^ 2 * (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ (2 * r) /
          (Y ^ 2 + (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ 2) *
          ‖QuantumNLS.Fourier.coeff L u.val n‖ ^ 2)) ∧
    (∀ Y : ℝ, 0 < Y → Continuous (fun u : Hk L (r - 1) =>
      (∫ t : ℝ, Y ^ 2 * t ^ (2 * r) / (Y ^ 2 + t ^ 2)
          ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) -
        ∑' n : ℤ, Y ^ 2 * (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ (2 * r) /
          (Y ^ 2 + (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ 2) *
          ‖QuantumNLS.Fourier.coeff L u.val n‖ ^ 2)) ∧
    (∀ B : Set (Hk L (r - 1)), Bornology.IsBounded B →
      ∃ C Y₀ : ℝ, 0 < C ∧ 0 < Y₀ ∧ ∀ u ∈ B, ∀ Y : ℝ, Y₀ ≤ Y →
        |(∫ t : ℝ, Y ^ 2 * t ^ (2 * r) / (Y ^ 2 + t ^ 2)
            ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) -
          ∑' n : ℤ, Y ^ 2 * (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ (2 * r) /
            (Y ^ 2 + (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ 2) *
            ‖QuantumNLS.Fourier.coeff L u.val n‖ ^ 2| ≤ C) := by
  exact QuantumNLS.Reg014Main.REG014 L κ hκ r hr

end QuantumNLS.REG014Spec
#print axioms QuantumNLS.REG014Spec.REG014_spec
