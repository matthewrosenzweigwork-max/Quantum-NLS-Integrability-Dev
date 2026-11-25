import NlsGge.GK38.DirichletRealPhase
import NlsGge.GK38.DirichletRealWeakCharacteristic
import NlsGge.GK38.EigenvalueCompactnessPhaseStability

/-! Actual varying-parameter weak phase limits and strong joint endpoint continuity. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem phaseCandidate_varyingWeak_uniform38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {x : ℕ → ℝ} {x₀ : ℝ} (hw : IsWeakLim u u₀) (hx : Tendsto x atTop (𝓝 x₀)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : DirichletTime38,
      |phaseCandidate38 (u k) (x k) t - phaseCandidate38 u₀ x₀ t| < ε := by
  have hz : Tendsto (fun k => (x k : ℂ)) atTop (𝓝 (x₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hx
  apply normalizedPhase_uniform_stability38
    (fun k t => dirichletState38 (u k) (x k : ℂ) t 0)
    (fun t => dirichletState38 u₀ (x₀ : ℂ) t 0)
    (fun k t => phaseCandidate38 (u k) (x k) t)
    (fun t => phaseCandidate38 u₀ x₀ t)
    (fun k => dirichlet_normalizedPhase38 (u k) (x k)) (dirichlet_normalizedPhase38 u₀ x₀)
  intro ε hε
  filter_upwards [dirichletState_varyingWeak_uniform38 hw hz hε] with k hk
  exact fun t => hk t 0

theorem phaseCandidate_varyingWeak_one38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {x : ℕ → ℝ} {x₀ : ℝ} (hw : IsWeakLim u u₀) (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun k => phaseCandidate38 (u k) (x k) 1) atTop
      (𝓝 (phaseCandidate38 u₀ x₀ 1)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [phaseCandidate_varyingWeak_uniform38 hw hx ε hε] with k hk
  simpa only [Real.dist_eq] using hk ⟨1, zero_le_one, le_rfl⟩

theorem continuous_phaseCandidate_one38 :
    Continuous (fun p : PhysicalL2 × ℝ => phaseCandidate38 p.1 p.2 1) := by
  rw [continuous_iff_seqContinuous]
  intro p p₀ hp
  exact phaseCandidate_varyingWeak_one38 (normLim_weakLim38 hp.fst_nhds) hp.snd_nhds

end
end NlsGge.GK38
