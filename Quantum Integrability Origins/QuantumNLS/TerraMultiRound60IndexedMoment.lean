import QuantumNLS.TerraMultiRound60MomentComparison
import QuantumNLS.Reg003CellLocalization
import QuantumNLS.RootWeightedMomentsR26

/-! All positive integer moment finiteness agrees with the indexed masses. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory Set
open scoped ENNReal
namespace QuantumNLS.TerraMultiRound60IndexedMoment
open QuantumNLS.PhysicalTensor QuantumNLS.RootWeightedCellsR26
open QuantumNLS.RootWeightedMomentsR26 QuantumNLS.TerraMultiRound60MomentComparison
variable {L κ : ℝ} [Fact (0 < L)]

theorem displacement_bound_ae (hκ : 0 < κ) (u : L2T L) :
    ∀ᵐ x ∂PhysicalQuantumMeasure.measure hκ u,
      ‖x - cellMomentum hκ u x‖ ≤ 2 * Real.sqrt (κ * ‖u‖^2 / L) := by
  have hloc := ae_all_iff.mpr (QuantumNLS.Reg003.loc_general hκ u)
  have hfib := ae_all_iff.mpr (ae_cell_fiber hκ u)
  filter_upwards [hloc, hfib] with x hx hf
  have hcell := (hf (cellIndex hκ u x)).mp rfl
  have hb := hx (cellIndex hκ u x) hcell
  change |x - (2 * Real.pi * (cellIndex hκ u x : ℝ) / L)| ≤ _
  apply abs_le.mpr
  constructor <;> linarith [hb.1, hb.2]

theorem indexed_moment_equivalence (hκ : 0 < κ) (u : L2T L)
    (p : ℕ) (hp : 0 < p) :
    Integrable (fun x : ℝ => ‖x‖^p) (PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => ‖momentum L n‖^p * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
  have hmeasure : IsFiniteMeasure (PhysicalQuantumMeasure.measure hκ u) := inferInstance
  have hd := bounded_displacement_moments (PhysicalQuantumMeasure.measure hκ u) p hp
    (fun x => x) (cellMomentum hκ u) measurable_id.aestronglyMeasurable
    (measurable_cellMomentum hκ u).aestronglyMeasurable _ (displacement_bound_ae hκ u)
  apply hd.trans
  have hm := integrable_map_measure (μ := PhysicalQuantumMeasure.measure hκ u)
    (g := fun n : ℤ => ‖momentum L n‖^p)
    (Measurable.of_discrete.aestronglyMeasurable)
    (measurable_cellIndex hκ u).aemeasurable
  change Integrable (fun x => ‖cellMomentum hκ u x‖^p)
      (PhysicalQuantumMeasure.measure hκ u) ↔ _
  change Integrable ((fun n : ℤ => ‖momentum L n‖^p) ∘ cellIndex hκ u)
      (PhysicalQuantumMeasure.measure hκ u) ↔ _
  apply hm.symm.trans
  change Integrable (fun n : ℤ => ‖momentum L n‖^p) (indexLaw hκ u) ↔ _
  rw [integrable_indexLaw_iff]
  simp only [Real.norm_eq_abs, abs_pow, abs_abs, mul_comm]

#print axioms displacement_bound_ae
#print axioms indexed_moment_equivalence
end QuantumNLS.TerraMultiRound60IndexedMoment
