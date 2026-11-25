import NlsGge.GK38.DirichletRealWeakMatrix
import NlsGge.GK38.DirichletRealBridge

/-! Varying weak actual Dirichlet state limits from all fundamental entries. -/
set_option autoImplicit false
open Filter Topology Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem dirichletState_varyingWeak_uniform38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {z : ℕ → ℂ} {z₀ : ℂ} (hw : IsWeakLim u u₀) (hz : Tendsto z atTop (𝓝 z₀))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ t : DirichletTime38, ∀ i : Fin 2,
      ‖dirichletState38 (u k) (z k) t i - dirichletState38 u₀ z₀ t i‖ < ε := by
  filter_upwards [fundPair_realSlice_varyingWeak_uniform38 hw hz (half_pos hε)] with k hk
  intro t i
  have ha := hk t i 0
  have hb := hk t i 1
  simp only [dirichletState38, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
  rw [add_sub_add_comm]
  exact (norm_add_le _ _).trans_lt (by linarith)

end
end NlsGge.GK38
