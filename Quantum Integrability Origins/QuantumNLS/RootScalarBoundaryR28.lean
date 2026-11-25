import QuantumNLS.RootScalarAbelR28

/-! The actual cell boundary identity in the principal-value convention. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.RootScalarBoundaryR28
open PhysicalTensor (L2T)
open RootHilbert RootScalarDensityR28 RootScalarAbelR28 RootDensityIdentification
open RootWeightedCellsR26
variable {L κ : ℝ} [Fact (0 < L)]

lemma reCauchy_density (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    IndexedScalarMeasure.reCauchy (PhysicalQuantumMeasure.measure hκ u) x ε =
      ∫ t,dens κ u (x-t)*LabelIdentification.kε ε t := by
  rw [LabelIdentification.reCauchy_eq _ hε,← density_measure hκ hu,
    integral_rhoMeasure (density_hyp hκ hu)]
  rw [← integral_sub_left_eq_self
    (fun t => dens κ u t*LabelIdentification.kε ε (x-t)) volume x]
  simp only [sub_sub_cancel]

lemma boundary_eq_pv (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) (x : ℝ) :
    Prop026Bound.reG hκ u x = hilbertPV (dens κ u) x := by
  apply tendsto_nhds_unique (Prop026Bound.boundary_pointwise hκ u x)
  apply (abel_limit (density_hyp hκ hu) x).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (reCauchy_density hκ hu hε x).symm

lemma displacement_pv (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    ∀ᵐ x ∂PhysicalQuantumMeasure.measure hκ u,
      x-cellMomentum hκ u x = (2*κ/L)*hilbertPV (dens κ u) x := by
  filter_upwards [ae_displacement_boundary hκ u] with x hx
  simpa only [boundary_eq_pv hκ hu x] using hx

end QuantumNLS.RootScalarBoundaryR28
