import NlsGge.GK38.DirichletRealWeakState

/-! Actual characteristic/antidiscriminant limits at varying weak spectral parameters. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem monodromyPair_realSlice_varyingWeak38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {z : ℕ → ℂ} {z₀ : ℂ} (hw : IsWeakLim u u₀) (hz : Tendsto z atTop (𝓝 z₀))
    (i j : Fin 2) : Tendsto (fun k => monodromyPair (realSlice (u k)) (z k) i j) atTop
      (𝓝 (monodromyPair (realSlice u₀) z₀ i j)) := by
  simp only [monodromyPair_eq_fundPair]
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [fundPair_realSlice_varyingWeak_uniform38 hw hz hε] with k hk
  simpa only [dist_eq_norm] using hk ⟨1, zero_le_one, le_rfl⟩ i j

theorem dirichletChar_realSlice_varyingWeak38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {z : ℕ → ℂ} {z₀ : ℂ} (hw : IsWeakLim u u₀) (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun k => dirichletChar (realSlice (u k)) (z k)) atTop
      (𝓝 (dirichletChar (realSlice u₀) z₀)) := by
  have he := monodromyPair_realSlice_varyingWeak38 hw hz
  have h := (((he 1 0).add (he 1 1)).sub (he 0 0)).sub (he 0 1) |>.div_const (2 * Complex.I)
  simpa only [dirichletChar_eq] using h

theorem antiDiscrim_realSlice_varyingWeak38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {z : ℕ → ℂ} {z₀ : ℂ} (hw : IsWeakLim u u₀) (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun k => antiDiscrim (realSlice (u k)) (z k)) atTop
      (𝓝 (antiDiscrim (realSlice u₀) z₀)) := by
  simpa only [antiDiscrim] using (monodromyPair_realSlice_varyingWeak38 hw hz 0 1).add
    (monodromyPair_realSlice_varyingWeak38 hw hz 1 0)

theorem dirichletChar_varyingWeak_root_limit38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {z : ℕ → ℂ} {z₀ : ℂ} (hw : IsWeakLim u u₀) (hz : Tendsto z atTop (𝓝 z₀))
    (hr : ∀ k, dirichletChar (realSlice (u k)) (z k) = 0) :
    dirichletChar (realSlice u₀) z₀ = 0 := by
  have h := dirichletChar_realSlice_varyingWeak38 hw hz
  have he : (fun k => dirichletChar (realSlice (u k)) (z k)) = fun _ => (0 : ℂ) := funext hr
  rw [he] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem normLim_weakLim38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    (h : Tendsto u atTop (𝓝 u₀)) : IsWeakLim u u₀ := fun _ =>
  tendsto_const_nhds.inner h

theorem weakLim_subseq38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    (hw : IsWeakLim u u₀) {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    IsWeakLim (u ∘ σ) u₀ := fun v => (hw v).comp hσ.tendsto_atTop

end
end NlsGge.GK38
