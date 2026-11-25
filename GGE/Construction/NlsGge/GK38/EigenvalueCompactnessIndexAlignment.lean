import NlsGge.GK38.EigenvalueCompactnessVaryingIndex
import NlsGge.GK38.EigenvalueCompactnessPhaseLimits

/-! # S7: converging actual periodic roots have their exact reference index -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem integer_halfturn_close38 (m n : ℤ)
    (h : |(m : ℝ) * Real.pi - (n : ℝ) * Real.pi| < Real.pi) : m = n := by
  have hd : |((m - n : ℤ) : ℝ)| < 1 := by
    rw [Int.cast_sub]
    rw [← sub_mul, abs_mul, abs_of_pos Real.pi_pos] at h
    nlinarith [Real.pi_pos]
  have hi : |m - n| < (1 : ℤ) := by exact_mod_cast hd
  have hi' := abs_lt.mp hi
  omega

theorem periodic_index_eventually_eq38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {x : ℕ → ℝ} {x₀ : ℝ} {m : ℕ → ℤ} {n : ℤ}
    (hw : IsWeakLim u u₀) (hx : Tendsto x atTop (𝓝 x₀))
    (hend : ∀ k, EndpointAt38 (u k) (m k) (x k)) (hend₀ : EndpointAt38 u₀ n x₀) :
    ∀ᶠ k in atTop, m k = n := by
  by_contra h
  obtain ⟨r, hr, hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp h)
  choose a he using (fun k => periodic_eigen_direction_exists38 (u (r k)) (m (r k)) (x (r k)) (hend (r k)))
  obtain ⟨a₀, ha₀, s, hs, has⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq
    (fun k => show a k ∈ sphere 0 1 from by simpa only [mem_sphere, dist_zero_right] using (he k).1)
  let q := r ∘ s
  have hq : StrictMono q := hr.comp hs
  have hwq : IsWeakLim (u ∘ q) u₀ := fun v => (hw v).comp hq.tendsto_atTop
  have hxq := hx.comp hq.tendsto_atTop
  have heq : ∀ k, EigenDirectionAt38 ((u ∘ q) k) ((x ∘ q) k) ((m ∘ q) k) ((a ∘ s) k) := fun k => he (s k)
  have hlim := eigenDirection_varyingIndex_limit38 hwq hxq has (fun k => hend (q k)) heq hend₀
  have hsmall := periodicPhase_varyingWeak_uniform38 hwq hxq has (fun k => (heq k).1) hlim.1 Real.pi_pos
  obtain ⟨k, hk⟩ := hsmall.exists
  have hval := hk ⟨1, zero_le_one, le_rfl⟩
  change |periodicPhase38 (u (q k)) (x (q k)) (a (s k)) 1 - periodicPhase38 u₀ x₀ a₀ 1| < Real.pi at hval
  have hp := periodicPhase_winding38 (u (q k)) (m (q k)) (x (q k)) (a (s k)) (hend (q k)) (he (s k))
  rw [hp, periodicPhase_winding38 u₀ n x₀ a₀ hend₀ hlim] at hval
  exact hbad (s k) (integer_halfturn_close38 _ n hval)

end
end NlsGge.GK38
