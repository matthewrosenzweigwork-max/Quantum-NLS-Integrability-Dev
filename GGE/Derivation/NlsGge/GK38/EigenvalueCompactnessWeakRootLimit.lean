import NlsGge.GK38.EigenvalueCompactnessEigenLimits

/-! # S7: actual varying weak roots converge to roots of the reference characteristic -/
set_option autoImplicit false
open Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem perChar_real_varyingWeak_tendsto38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {x : ℕ → ℝ} {x₀ : ℝ} (hw : IsWeakLim u u₀) (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun k => perChar (realSlice (u k)) (x k : ℂ)) atTop
      (𝓝 (perChar (realSlice u₀) (x₀ : ℂ))) := by
  have hM := monodromy_realSlice_varyingWeak_tendsto38 hw hx
  have h0 := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hM 0) 0
  have h1 := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hM 1) 1
  have hD := h0.add h1
  simpa only [perChar, perCharOf, discrim, Matrix.trace_fin_two] using hD.pow 2 |>.sub_const (4 : ℂ)

theorem perChar_real_varyingWeak_root_limit38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {x : ℕ → ℝ} {x₀ : ℝ} (hw : IsWeakLim u u₀) (hx : Tendsto x atTop (𝓝 x₀))
    (hr : ∀ k, perChar (realSlice (u k)) (x k : ℂ) = 0) :
    perChar (realSlice u₀) (x₀ : ℂ) = 0 := by
  have he := perChar_real_varyingWeak_tendsto38 hw hx
  have hz : (fun k => perChar (realSlice (u k)) (x k : ℂ)) = fun _ => (0 : ℂ) := funext hr
  rw [hz] at he
  exact tendsto_nhds_unique he tendsto_const_nhds

end
end NlsGge.GK38
