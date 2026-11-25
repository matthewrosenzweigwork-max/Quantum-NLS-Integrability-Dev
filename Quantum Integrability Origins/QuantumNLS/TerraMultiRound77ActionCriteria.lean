import QuantumNLS.TerraMultiRound77LowEquivalence
import QuantumNLS.TerraMultiRound69FractionalCells

/-! Actual indexed action criterion at low fractional orders. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.RootWeightedCellsR26
open QuantumNLS.TerraMultiRound69FractionalCells QuantumNLS.TerraMultiRound77LowEquivalence
namespace QuantumNLS.TerraMultiRound77ActionCriteria

/-- For any finite measure, shifting the absolute-value weight by one does
not change the finiteness of a positive real power. -/
theorem shifted_power_iff (μ : Measure ℝ) [IsFiniteMeasure μ] (p : ℝ) (hp : 0 < p) :
    Integrable (fun x : ℝ => (1+|x|)^p) μ ↔
      Integrable (fun x : ℝ => |x|^p) μ := by
  have h := bounded_displacement_rpow μ p hp (fun x : ℝ => |x|) (fun x : ℝ => 1+|x|)
    measurable_abs.aestronglyMeasurable (measurable_const.add measurable_abs).aestronglyMeasurable
    1 (by apply ae_of_all; intro x; simp)
  have hn : ∀ x : ℝ, abs (1 + |x|) = 1+|x| := fun x => abs_of_nonneg (by positivity)
  simp only [Real.norm_eq_abs, abs_abs, hn] at h
  exact h.symm

/-- At every positive order, the physical fractional moment is finite exactly
when the actual indexed weighted action series is summable. -/
theorem physical_power_iff_indexed_actions {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : L2T L) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
  exact (shifted_power_iff (PhysicalQuantumMeasure.measure hκ u) (2*s) (by positivity)).symm.trans
    (shifted_indexed_rpow_iff hκ u (2*s) (by positivity))

/-- The free fractional moment and the physical weighted actions have the
same finiteness for every L² field when 0<s<1/2. -/
theorem free_power_iff_indexed_actions_L2 {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : L2T L) (s : ℝ) (hs0 : 0 < s) (hs : s < 1/2) :
    Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L u) ↔
      Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
  exact (physical_free_moment_iff_L2 hκ u s hs0 hs).symm.trans
    (physical_power_iff_indexed_actions hκ u s hs0)

#print axioms shifted_power_iff
#print axioms physical_power_iff_indexed_actions
#print axioms free_power_iff_indexed_actions_L2
end QuantumNLS.TerraMultiRound77ActionCriteria
