import NlsGge.GK38.PairCompact

/-! Weak real-slice transport, proved from the actual L2 inner product. -/
set_option autoImplicit false
open Filter Topology MeasureTheory
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem physicalL2_inner_star38 (v u : PhysicalL2) :
    inner ℂ v (star u) = star (inner ℂ (star v) u) := by
  have hi := L2.integrable_inner (𝕜 := ℂ) (star v) u
  rw [L2.inner_def, L2.inner_def, Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u, Lp.coeFn_star v] with x hu hv
  rw [hu, hv]
  simp only [Pi.star_apply, RCLike.inner_apply, Complex.star_def, map_mul,
    Complex.conj_conj]

theorem weakLim_star38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2} (hw : IsWeakLim u u₀) :
    IsWeakLim (fun k => star (u k)) (star u₀) := by
  intro v
  simp_rw [physicalL2_inner_star38, Complex.star_def]
  exact Complex.continuous_conj.continuousAt.tendsto.comp (hw (star v))

theorem weakLim_realSlice38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2} (hw : IsWeakLim u u₀) :
    IsWeakLimComp (fun k => realSlice (u k)) (realSlice u₀) :=
  ⟨hw, weakLim_star38 hw⟩

end
end NlsGge.GK38
