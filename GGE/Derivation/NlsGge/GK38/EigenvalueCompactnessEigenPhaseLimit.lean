import NlsGge.GK38.EigenvalueCompactnessEigenLimits
import NlsGge.GK38.EigenvalueCompactnessDirectionIndependence

/-! # S7: compact eigendirections yield the unique limiting half-turn

No direction is selected continuously across potentials.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem periodicPhase_eigen_tendsto38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {x : ℕ → ℝ} {x₀ : ℝ} {a : ℕ → ℂ} {b : ℂ} {n : ℤ}
    (hw : IsWeakLim u u₀) (hx : Tendsto x atTop (𝓝 x₀))
    (he : ∀ k, EigenDirectionAt38 (u k) (x k) n (a k))
    (hb : EigenDirectionAt38 u₀ x₀ n b) :
    Tendsto (fun k => periodicPhase38 (u k) (x k) (a k) 1) atTop
      (𝓝 (periodicPhase38 u₀ x₀ b 1)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra h
  have hfreq : ∃ᶠ k in atTop,
      ε ≤ dist (periodicPhase38 (u k) (x k) (a k) 1) (periodicPhase38 u₀ x₀ b 1) := by
    simpa only [not_lt] using not_eventually.mp h
  obtain ⟨r, hr, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨a₀, ha₀, s, hs, has⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq
    (fun k => show a (r k) ∈ sphere 0 1 from by simpa only [mem_sphere, dist_zero_right] using (he (r k)).1)
  let q := r ∘ s
  have hq : StrictMono q := hr.comp hs
  have hwq : IsWeakLim (u ∘ q) u₀ := fun v => (hw v).comp hq.tendsto_atTop
  have hxq : Tendsto (x ∘ q) atTop (𝓝 x₀) := hx.comp hq.tendsto_atTop
  have haq : Tendsto (a ∘ q) atTop (𝓝 a₀) := by simpa only [q, Function.comp_def] using! has
  have heq : ∀ k, EigenDirectionAt38 ((u ∘ q) k) ((x ∘ q) k) n ((a ∘ q) k) := fun k => he (q k)
  have he₀ := eigenDirection_varyingWeak_limit38 hwq hxq haq heq
  have hunit₀ : ‖a₀‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using ha₀
  have hpeq := periodicPhase_direction_independent38 u₀ x₀ n a₀ b he₀ hb
  have hsmall := periodicPhase_varyingWeak_uniform38 hwq hxq haq (fun k => (heq k).1) hunit₀ hε
  obtain ⟨k, hk⟩ := hsmall.exists
  have hval := hk ⟨1, zero_le_one, le_rfl⟩
  rw [hpeq] at hval
  have hlarge := hbad (s k)
  change ε ≤ dist (periodicPhase38 ((u ∘ q) k) ((x ∘ q) k) ((a ∘ q) k) 1) (periodicPhase38 u₀ x₀ b 1) at hlarge
  rw [Real.dist_eq] at hlarge
  exact (not_lt_of_ge hlarge) hval

end
end NlsGge.GK38
