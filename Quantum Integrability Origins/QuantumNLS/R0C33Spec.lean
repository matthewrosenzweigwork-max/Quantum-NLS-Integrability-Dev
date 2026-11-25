import QuantumNLS.D05TotalVariation
/-! integrator-authored trusted spec for R-0C33082D prop:D05-total-variation (Terra r156 ACCEPT): headline statement(s) copied verbatim from D05TotalVariation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
namespace R0C33Spec
open QuantumNLS.D05TotalVariation
open QuantumNLS.TotalVariation (tvNorm tvNorm_mutuallySingular tvNorm_zero_right tvNorm_le_density)
open QuantumNLS.FullMass (Mmeas Mmeas_univ Mmeas_zero Mmeas_zero_coupling Mfin)
open QuantumNLS.RootDensityIdentification (dens continuous_dens dens_nonneg root_density measure_absolutelyContinuous)
open QuantumNLS.FreeLimit (freeMeasure)
open QuantumNLS.PhysicalTensor (L2T)
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem prop_D05_total_variation_spec :
    (∀ κ0 : ℝ, 0 < κ0 → ∀ u0 : L2T L,
      Tendsto (fun p : ℝ × L2T L => tvNorm (Mmeas p.1 p.2) (Mmeas κ0 u0)) (𝓝 (κ0, u0)) (𝓝 0)) ∧
    (∀ u : L2T L, u ≠ 0 →
      Tendsto (fun x : {κ : ℝ // 0 ≤ κ} => Mfin x.1 u) (𝓝 ⟨0, le_rfl⟩) (𝓝 (Mfin 0 u)) ∧
      (∀ κ : ℝ, 0 < κ → tvNorm (Mmeas κ u) (Mmeas 0 u) = 2 * ENNReal.ofReal (‖u‖ ^ 2)) ∧
      ¬ Tendsto (fun κ : ℝ => tvNorm (Mmeas κ u) (Mmeas 0 u)) (𝓝[>] 0) (𝓝 0)) := by
  first
  | exact QuantumNLS.D05TotalVariation.prop_D05_total_variation
  | (apply QuantumNLS.D05TotalVariation.prop_D05_total_variation <;> assumption)

end R0C33Spec
#print axioms R0C33Spec.prop_D05_total_variation_spec
