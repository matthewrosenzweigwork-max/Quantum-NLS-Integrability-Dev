import NlsGge.GK38.DirichletRealWeakTransport

/-! Full-time varying-spectral-parameter weak convergence of actual fundamental entries.
Only accepted F3/F6 and weak real-slice transport are used. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem fundPair_entry_difference_le_norm38 (φ : PotPair) (z w : ℂ)
    (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖fundPair φ z t i j - fundPair φ w t i j‖ ≤ ‖fundContP φ z - fundContP φ w‖ := by
  change ‖((fundContP φ z - fundContP φ w) t) i j‖ ≤ ‖fundContP φ z - fundContP φ w‖
  exact (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans
    ((fundContP φ z - fundContP φ w).norm_coe_le_norm t))

theorem continuous_fundContP_spectral38 (φ : PotPair) :
    Continuous (fun z : ℂ => fundContP φ z) := by
  have hJ : Continuous (fun p : PotPair × ℂ => fundContP p.1 p.2) :=
    continuousOn_univ.mp analyticOnNhd_fundContP.continuousOn
  have hA : Continuous (fun z : ℂ => (φ, z)) := continuous_const.prodMk continuous_id
  have hcomp := hJ.comp hA
  simpa only [Function.comp_def] using hcomp

theorem fundPair_varyingWeak_uniform38 {φ : ℕ → PotPair} {φ₀ : PotPair}
    {z : ℕ → ℂ} {z₀ : ℂ} (hw : IsWeakLimComp φ φ₀) (hz : Tendsto z atTop (𝓝 z₀))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ t : Icc (0 : ℝ) 1, ∀ i j : Fin 2,
      ‖fundPair (φ k) (z k) t i j - fundPair φ₀ z₀ t i j‖ < ε := by
  have hK : ∀ᶠ k in atTop, z k ∈ closedBall z₀ 1 :=
    hz.eventually (mem_of_superset (ball_mem_nhds z₀ one_pos) ball_subset_closedBall)
  have hF : Tendsto (fun k => fundContP φ₀ (z k)) atTop (𝓝 (fundContP φ₀ z₀)) :=
    (continuous_fundContP_spectral38 φ₀).continuousAt.tendsto.comp hz
  have hsmall : ∀ᶠ k in atTop, ‖fundContP φ₀ (z k) - fundContP φ₀ z₀‖ < ε / 2 := by
    simpa only [mem_ball, dist_eq_norm] using
      hF.eventually (ball_mem_nhds (fundContP φ₀ z₀) (half_pos hε))
  filter_upwards [hK, hsmall,
    fundPair_weakContinuous_uniform38 hw (isCompact_closedBall z₀ 1) (half_pos hε)] with k hk hs hf
  intro t i j
  have ha := hf (z k) hk t i j
  have hb := (fundPair_entry_difference_le_norm38 φ₀ (z k) z₀ t i j).trans_lt hs
  have ht := norm_add_le (fundPair (φ k) (z k) t i j - fundPair φ₀ (z k) t i j)
    (fundPair φ₀ (z k) t i j - fundPair φ₀ z₀ t i j)
  rw [sub_add_sub_cancel] at ht
  linarith

theorem fundPair_realSlice_varyingWeak_uniform38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {z : ℕ → ℂ} {z₀ : ℂ} (hw : IsWeakLim u u₀) (hz : Tendsto z atTop (𝓝 z₀))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ t : Icc (0 : ℝ) 1, ∀ i j : Fin 2,
      ‖fundPair (realSlice (u k)) (z k) t i j - fundPair (realSlice u₀) z₀ t i j‖ < ε :=
  fundPair_varyingWeak_uniform38 (weakLim_realSlice38 hw) hz hε

end
end NlsGge.GK38
