import QuantumNLS.RootOccupationLimit

/-! An accepted occupation-limit consequence needed for binding the actual
contour Hamiltonian's product-state principal symbol. No interpretation of
DEF-043 is introduced: RootOccupationLimit is used read-only. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology MeasureTheory
namespace QuantumNLS.IndexedOccupationLimitR30b
open PhysicalTensor RootOccupationLimit BulkResponseActual EmpiricalRapidity
variable {L κ : ℝ} [Fact (0 < L)]

/-- Each actual Born-law occupation expectation tends to the corresponding
physical indexed mass, for arbitrary unit L2 profiles and positive coupling. -/
theorem component_limit (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (n : ℤ) :
    Tendsto (fun N : ℕ => ∫ m, (m.1 n : ℝ)/(N : ℝ)
      ∂(bornMeasure (physBasis L hκ N) u hu)) atTop
      (𝓝 ((RootIndexedMasses.masses hκ u).1 n)) := by
  have ht := occDist_Lp hκ u hu one_pos
  simp only [Real.rpow_one] at ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ ht
  filter_upwards [eventually_gt_atTop 0] with N hN
  have he := expected_l1 hκ u hu hN
  exact (show ‖(∫ m, (m.1 n : ℝ)/(N : ℝ)
      ∂(bornMeasure (physBasis L hκ N) u hu))-(RootIndexedMasses.masses hκ u).1 n‖ ≤
      ∑' j : ℤ, |(∫ m, (m.1 j : ℝ)/(N : ℝ)
        ∂(bornMeasure (physBasis L hκ N) u hu))-(RootIndexedMasses.masses hκ u).1 j| from by
    rw [Real.norm_eq_abs]
    exact Summable.le_tsum he.1 n (fun j _ => abs_nonneg _)).trans he.2

end QuantumNLS.IndexedOccupationLimitR30b
#print axioms QuantumNLS.IndexedOccupationLimitR30b.component_limit
