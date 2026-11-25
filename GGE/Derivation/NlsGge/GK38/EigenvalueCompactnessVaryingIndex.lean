import NlsGge.GK38.EigenvalueCompactnessEigenLimits
import NlsGge.GK38.EigenvalueCompactnessWinding

/-! # S7: actual trace transport for varying endpoint indices -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem monodromy_trace_realSlice_varyingWeak38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {x : ℕ → ℝ} {x₀ : ℝ} (hw : IsWeakLim u u₀) (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun k => (monodromyPair (realSlice (u k)) (x k : ℂ)).trace) atTop
      (𝓝 ((monodromyPair (realSlice u₀) (x₀ : ℂ)).trace)) := by
  have hM := monodromy_realSlice_varyingWeak_tendsto38 hw hx
  have h0 := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hM 0) 0
  have h1 := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hM 1) 1
  simpa only [Matrix.trace_fin_two] using h0.add h1

theorem eigenDirection_varyingIndex_limit38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {x : ℕ → ℝ} {x₀ : ℝ} {a : ℕ → ℂ} {a₀ : ℂ} {m : ℕ → ℤ} {n : ℤ}
    (hw : IsWeakLim u u₀) (hx : Tendsto x atTop (𝓝 x₀))
    (ha : Tendsto a atTop (𝓝 a₀)) (hend : ∀ k, EndpointAt38 (u k) (m k) (x k))
    (he : ∀ k, EigenDirectionAt38 (u k) (x k) (m k) (a k))
    (hend₀ : EndpointAt38 u₀ n x₀) : EigenDirectionAt38 u₀ x₀ n a₀ := by
  have hu : ‖a₀‖ = 1 :=
    tendsto_nhds_unique ha.norm (by simpa only [(he _).1] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  have ht := (monodromy_trace_realSlice_varyingWeak38 hw hx).div_const (2 : ℂ)
  have hc : Tendsto (fun k => (Real.cos ((m k : ℝ) * Real.pi) : ℂ)) atTop
      (𝓝 (Real.cos ((n : ℝ) * Real.pi) : ℂ)) := by
    have heq (k : ℕ) : (monodromyPair (realSlice (u k)) (x k : ℂ)).trace / 2 =
        (Real.cos ((m k : ℝ) * Real.pi) : ℂ) := by
      rw [endpoint_trace38 _ _ _ (hend k)]
      ring
    rw [endpoint_trace38 u₀ n x₀ hend₀] at ht
    have hlim : (2 * (Real.cos ((n : ℝ) * Real.pi) : ℂ)) / 2 =
        (Real.cos ((n : ℝ) * Real.pi) : ℂ) := by ring
    rw [hlim] at ht
    exact ht.congr' (Eventually.of_forall heq)
  have hA := realInitial_continuous38.continuousAt.tendsto.comp ha
  have hL := matrix_mulVec_tendsto38 (monodromy_realSlice_varyingWeak_tendsto38 hw hx) hA
  have hR := hc.smul hA
  refine ⟨hu, ?_⟩
  exact tendsto_nhds_unique hL (hR.congr' (Eventually.of_forall (fun k => (he k).2.symm)))

end
end NlsGge.GK38
