import NlsGge.GK38.EigenvalueCompactnessWeakDirections
import NlsGge.GK38.EigenvalueCompactnessDirections

/-! # S7: closed actual eigendirection equations under weak limits -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem monodromy_realSlice_varyingWeak_tendsto38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {x : ℕ → ℝ} {x₀ : ℝ} (hw : IsWeakLim u u₀) (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun k => monodromyPair (realSlice (u k)) (x k : ℂ)) atTop
      (𝓝 (monodromyPair (realSlice u₀) (x₀ : ℂ))) := by
  have hz := Complex.continuous_ofReal.continuousAt.tendsto.comp hx
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [fundPair_realSlice_varyingWeak_uniform38 hw hz hε] with k hk
  simpa only [monodromyPair_eq_fundPair, dist_eq_norm, Function.comp_def] using hk ⟨1, zero_le_one, le_rfl⟩ i j

theorem realInitial_continuous38 : Continuous realInitial38 := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [realInitial38, Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact continuous_id
  · exact continuous_star

theorem continuous_matrix_mulVec38 :
    Continuous (fun p : Matrix (Fin 2) (Fin 2) ℂ × (Fin 2 → ℂ) => p.1.mulVec p.2) := by
  exact continuous_fst.matrix_mulVec continuous_snd

theorem matrix_mulVec_tendsto38 {M : ℕ → Matrix (Fin 2) (Fin 2) ℂ}
    {M₀ : Matrix (Fin 2) (Fin 2) ℂ} {v : ℕ → Fin 2 → ℂ} {v₀ : Fin 2 → ℂ}
    (hM : Tendsto M atTop (𝓝 M₀)) (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun k => (M k).mulVec (v k)) atTop (𝓝 (M₀.mulVec v₀)) := by
  exact continuous_matrix_mulVec38.continuousAt.tendsto.comp (hM.prodMk_nhds hv)

theorem eigenDirection_varyingWeak_limit38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {x : ℕ → ℝ} {x₀ : ℝ} {a : ℕ → ℂ} {a₀ : ℂ} {n : ℤ}
    (hw : IsWeakLim u u₀) (hx : Tendsto x atTop (𝓝 x₀))
    (ha : Tendsto a atTop (𝓝 a₀)) (he : ∀ k, EigenDirectionAt38 (u k) (x k) n (a k)) :
    EigenDirectionAt38 u₀ x₀ n a₀ := by
  have hu : ‖a₀‖ = 1 := by
    exact tendsto_nhds_unique (ha.norm) (by simpa only [(he _).1] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  refine ⟨hu, ?_⟩
  have hM := monodromy_realSlice_varyingWeak_tendsto38 hw hx
  have hA := realInitial_continuous38.continuousAt.tendsto.comp ha
  have hL : Tendsto (fun k => (monodromyPair (realSlice (u k)) (x k : ℂ)).mulVec (realInitial38 (a k))) atTop
      (𝓝 ((monodromyPair (realSlice u₀) (x₀ : ℂ)).mulVec (realInitial38 a₀))) := by
    exact matrix_mulVec_tendsto38 hM hA
  have hR := hA.const_smul (Real.cos ((n : ℝ) * Real.pi) : ℂ)
  exact tendsto_nhds_unique hL (hR.congr' (Eventually.of_forall (fun k => (he k).2.symm)))

end
end NlsGge.GK38
