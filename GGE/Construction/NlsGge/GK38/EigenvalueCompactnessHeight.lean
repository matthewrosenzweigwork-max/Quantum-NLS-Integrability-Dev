import NlsGge.GK38.EigenvalueCompactnessDefs

/-! # S7: joint all-L2 gap height continuity and integral prerequisites

The actual arcosh height is treated before the totalized action integral.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

set_option maxHeartbeats 800000 in
theorem gapHeight_joint_continuous_L2_38 :
    Continuous (fun p : PhysicalL2 × ℝ => actualGapHeightE02_38 p.1 p.2) := by
  have hm : Continuous (fun p : PhysicalL2 × ℝ => (realSlice p.1, (p.2 : ℂ))) :=
    (continuous_realSlice.comp (continuous_fst : Continuous (fun p : PhysicalL2 × ℝ => p.1))).prodMk
      (Complex.continuous_ofReal.comp (continuous_snd : Continuous (fun p : PhysicalL2 × ℝ => p.2)))
  have hc : Continuous (fun p : PhysicalL2 × ℝ => discrim (realSlice p.1) (p.2 : ℂ)) :=
    by simpa only [Function.comp_def] using discrim_L2_continuous.comp hm
  have hh : Continuous (fun p : PhysicalL2 × ℝ => actualPhysicalUnitHalfTrace32 p.1 (p.2 : ℂ)) := by
    have he : (fun p : PhysicalL2 × ℝ => actualPhysicalUnitHalfTrace32 p.1 (p.2 : ℂ)) =
        fun p => discrim (realSlice p.1) (p.2 : ℂ) / 2 := by
      funext p; rw [discrim_realSlice]; ring
    rw [he]
    exact hc.div_const 2
  exact Real.continuousOn_arcosh.comp_continuous (continuous_const.max hh.norm)
    (fun _ => mem_Ici.mpr (le_max_left _ _))

set_option maxHeartbeats 800000 in
theorem gapHeight_uniform_strong38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hu : Tendsto u atTop (𝓝 u₀)) (A B : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ Icc A B,
      |actualGapHeightE02_38 (u k) x - actualGapHeightE02_38 u₀ x| < ε := by
  let : CompactSpace (Icc A B) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hm : Continuous (fun p : PhysicalL2 × Icc A B => (p.1, (p.2 : ℝ))) :=
    (continuous_fst : Continuous (fun p : PhysicalL2 × Icc A B => p.1)).prodMk
      (continuous_subtype_val.comp (continuous_snd : Continuous (fun p : PhysicalL2 × Icc A B => p.2)))
  have hc : Continuous (fun p : PhysicalL2 × Icc A B => actualGapHeightE02_38 p.1 p.2) :=
    by simpa only [Function.comp_def] using gapHeight_joint_continuous_L2_38.comp hm
  let Φ : C(PhysicalL2, C(Icc A B, ℝ)) := ContinuousMap.curry ⟨_, hc⟩
  have he : ∀ᶠ k in atTop, dist (Φ (u k)) (Φ u₀) < ε :=
    ((Φ.continuous.tendsto u₀).comp hu).eventually (ball_mem_nhds _ hε)
  filter_upwards [he] with k hk x hx
  have hm := (ContinuousMap.dist_apply_le_dist (f := Φ (u k)) (g := Φ u₀) ⟨x, hx⟩).trans_lt hk
  simpa only [Φ, ContinuousMap.curry_apply, ContinuousMap.coe_mk, Real.dist_eq] using hm

theorem gapAction_intervalIntegrable_L2_38 (u : PhysicalL2) (n : ℤ) :
    IntervalIntegrable (actualGapHeightE02_38 u) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
  (continuous_actualGapHeightE02_38 u).intervalIntegrable _ _

end
end NlsGge.GK38
