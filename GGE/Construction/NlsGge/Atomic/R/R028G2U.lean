import Mathlib
import NlsGge.Atomic.R.R028G2
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Sobolev.WeightedProjection

                                                                                                   
                                                                                                             
                                                                                                               
                                                                                                                  
                                                                                                            
                                                                                                                
                                                                                                                        
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter
open scoped Topology

namespace NlsGge.ThirdConsultation.R
noncomputable section
section R028G2U
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)

/-- The head point of the coordinates of `x` is the ambient projection of `x`. -/
theorem r028u_headToE_eq (N : ℕ) (x : RamerE c s) :
    NlsGge.Ramer.headToE c s N (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x)) =
      ambientProjection c s N x := by
  have hz : ∀ n : ℤ, (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from
      NlsGge.Measure.fullWeightedSequenceRealization c s (NlsGge.Ramer.coordE c s x)) n =
        NlsGge.Ramer.coordE c s x n := by
    intro n
    rw [NlsGge.Ramer.realization_coordE] <;> rfl
  rw [NlsGge.Ramer.headToE_headPt_eq c s N _ hz, NlsGge.Ramer.realization_coordE]
  rfl

/-- The ambient projection is linear. -/
theorem r028u_proj_sub (N : ℕ) (v w : RamerE c s) :
    ambientProjection c s N (v - w) = ambientProjection c s N v - ambientProjection c s N w :=
  map_sub (NlsGge.Pilot.weightedProjectionContinuous (NlsGge.Pilot.fullModeWeight c s)
    (NlsGge.Pilot.symmetricModes N)) v w

/-- The ambient projection is a contraction. -/
theorem r028u_proj_dist (N : ℕ) (x y : RamerE c s) :
    dist (ambientProjection c s N x) (ambientProjection c s N y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← r028u_proj_sub c s N x y]
  exact NlsGge.Pilot.weightedProjection_norm_le (NlsGge.Pilot.fullModeWeight c s)
    (NlsGge.Pilot.symmetricModes N) (x - y)

include hs in
/-- **G2U, uniform locality.** If `K = G` on `ball x₀ r`, then for some `N₀` and all `N ≥ N₀` and all
`x ∈ ball x₀ (r/4)`, `ramerApprox` and `literalCylDiv` of `K` and `G` agree at `x`. -/
theorem r028_locality_uniform (x₀ : RamerE c s) (r : ℝ) (hr : 0 < r) (K G : RamerE c s → RamerH c)
    (hEq : EqOn K G (ball x₀ r)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ x ∈ ball x₀ (r / 4),
      ramerApprox c s hs K N x = ramerApprox c s hs G N x ∧
        literalCylDiv c s K N x = literalCylDiv c s G N x := by
  have ht := r028g2_headPt_tendsto c s x₀
  have hev : ∀ᶠ N : ℕ in atTop,
      dist (NlsGge.Ramer.headToE c s N (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x₀))) x₀
        < r / 2 :=
    (Metric.tendsto_nhds.1 ht) (r / 2) (half_pos hr)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN x hx => ?_⟩
  have hxd : dist x x₀ < r / 4 := hx
  have hdist : dist (NlsGge.Ramer.headToE c s N (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x)))
      (NlsGge.Ramer.headToE c s N (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x₀))) ≤ dist x x₀ := by
    rw [r028u_headToE_eq c s N x, r028u_headToE_eq c s N x₀]
    exact r028u_proj_dist c s N x x₀
  have hy : NlsGge.Ramer.headToE c s N (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x)) ∈
      ball x₀ r := by
    rw [Metric.mem_ball]
    have htri := dist_triangle
      (NlsGge.Ramer.headToE c s N (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x)))
      (NlsGge.Ramer.headToE c s N (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x₀))) x₀
    have h2 := hN₀ N hN
    linarith
  have hxr : x ∈ ball x₀ r := by
    rw [Metric.mem_ball] at hx ⊢
    linarith
  have hKGx : K =ᶠ[𝓝 x] G :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hxr) (fun y hy => hEq hy)
  have hKGy : ∀ᶠ y in 𝓝 (NlsGge.Ramer.headToE c s N (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x))),
      K y = G y :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hy) (fun y hy' => hEq hy')
  exact ⟨r028g2_ramerApprox_eq c s hs K G x hKGx N, r028g2_literalCylDiv_eq c s K G N x hKGy⟩

end R028G2U
end
end NlsGge.ThirdConsultation.R
