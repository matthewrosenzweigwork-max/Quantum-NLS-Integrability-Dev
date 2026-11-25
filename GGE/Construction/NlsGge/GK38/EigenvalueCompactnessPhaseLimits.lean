import NlsGge.GK38.EigenvalueCompactnessWeakDirections
import NlsGge.GK38.EigenvalueCompactnessPhaseRealization
import NlsGge.GK38.EigenvalueCompactnessPhaseStability

/-! # S7: actual phase lift limits for varying spectral parameters and directions -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem periodicPhase_normalized38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : ‖a‖ = 1) :
    NormalizedPhase38 (normalizedFirst38 u x a) (fun t : Time38 => periodicPhase38 u x a t) := by
  obtain ⟨hc, hz, he⟩ := periodicPhase_realization38 u x a ha
  refine ⟨?_, continuousOn_iff_continuous_domRestrict.mp hc, hz, he⟩
  unfold normalizedFirst38
  apply Continuous.div_const
  have hC := (fundContP (realSlice u) (x : ℂ)).continuous
  have h0 : Continuous (fun t : Time38 => fundPair (realSlice u) (x : ℂ) t 0 0) :=
    (continuous_apply 0).comp ((continuous_apply 0).comp hC)
  have h1 : Continuous (fun t : Time38 => fundPair (realSlice u) (x : ℂ) t 0 1) :=
    (continuous_apply 1).comp ((continuous_apply 0).comp hC)
  simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.mul_apply, Pi.add_apply] using!
    (h0.mul continuous_const).add (h1.mul continuous_const)

theorem periodicPhase_varyingWeak_uniform38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {x : ℕ → ℝ} {x₀ : ℝ} {a : ℕ → ℂ} {a₀ : ℂ}
    (hw : IsWeakLim u u₀) (hx : Tendsto x atTop (𝓝 x₀))
    (ha : Tendsto a atTop (𝓝 a₀)) (hunit : ∀ k, ‖a k‖ = 1) (hunit₀ : ‖a₀‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ t : Time38,
      |periodicPhase38 (u k) (x k) (a k) t - periodicPhase38 u₀ x₀ a₀ t| < ε := by
  apply normalizedPhase_uniform_stability38
    (fun k => normalizedFirst38 (u k) (x k) (a k)) (normalizedFirst38 u₀ x₀ a₀)
    (fun k t => periodicPhase38 (u k) (x k) (a k) t) (fun t => periodicPhase38 u₀ x₀ a₀ t)
    (fun k => periodicPhase_normalized38 _ _ _ (hunit k))
    (periodicPhase_normalized38 _ _ _ hunit₀)
    (fun δ hδ => normalizedFirst_varyingWeak_uniform38 hw hx ha hunit hunit₀ hδ) ε hε

theorem periodicPhase_direction_continuous38 (u : PhysicalL2) (x : ℝ) :
    ContinuousOn (fun a : ℂ => periodicPhase38 u x a 1) (sphere 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_iff_seqContinuous.mpr
  intro a a₀ ha
  have hu : ∀ k, ‖(a k : ℂ)‖ = 1 := fun k => by
    simpa only [mem_sphere, dist_zero_right] using (a k).property
  have hu₀ : ‖(a₀ : ℂ)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using a₀.property
  have hc : Tendsto (fun k => (a k : ℂ)) atTop (𝓝 (a₀ : ℂ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp ha
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [periodicPhase_varyingWeak_uniform38 (isWeakLim_const u) tendsto_const_nhds hc hu hu₀ hε] with k hk
  change dist (periodicPhase38 u x (a k) 1) (periodicPhase38 u x a₀ 1) < ε
  rw [Real.dist_eq]
  exact hk ⟨1, zero_le_one, le_rfl⟩

end
end NlsGge.GK38
