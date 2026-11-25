import Mathlib
import NlsGge.Atomic.LIB.LIB079
import NlsGge.ThirdConsultation.G2.G2037C5B1

                                                                                                    
                                                                                                              
                                                                                                     
                                                                            
                                                                                                        
                                                        
                                                                                                         
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open scoped unitInterval
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G2037P2Aux

/-- Straight-line contraction of a gap cycle to the disc centre: `H(s,t) = c + (1 - s)(γ t - c)`. -/
def contractH (D : DiscWithSegment) : C(I × I, ℂ) :=
  ⟨fun p => D.center + (((1 - (p.1 : ℝ)) : ℝ) : ℂ) * (gapCycle D p.2 - D.center), by
    refine continuous_const.add (Continuous.mul ?_ ?_)
    · exact Complex.continuous_ofReal.comp (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
    · exact ((gapCycle D).continuous.comp continuous_snd).sub continuous_const⟩

theorem contractH_zero (D : DiscWithSegment) (t : I) : contractH D (0, t) = gapCycle D t := by
  simp [contractH]

theorem contractH_one (D : DiscWithSegment) (t : I) : contractH D (1, t) = D.center := by
  simp [contractH]

theorem contractH_closed (D : DiscWithSegment) (s : I) : contractH D (s, 0) = contractH D (s, 1) := by
  simp only [contractH, ContinuousMap.coe_mk, (gapCycle D).source, (gapCycle D).target]

theorem contractH_range (D : DiscWithSegment) : range (contractH D) ⊆ ball D.center D.radius := by
  rintro _ ⟨p, rfl⟩
  have h1 : gapCycle D p.2 ∈ ball D.center D.radius := (gapCycle_range D ⟨p.2, rfl⟩).1
  have hs0 : (0 : ℝ) ≤ 1 - (p.1 : ℝ) := by linarith [p.1.2.2]
  have hs1 : 1 - (p.1 : ℝ) ≤ 1 := by linarith [p.1.2.1]
  rw [mem_ball, dist_eq_norm] at h1 ⊢
  show ‖D.center + (((1 - (p.1 : ℝ)) : ℝ) : ℂ) * (gapCycle D p.2 - D.center) - D.center‖ < D.radius
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
  have hle : (1 - (p.1 : ℝ)) * ‖gapCycle D p.2 - D.center‖ ≤ ‖gapCycle D p.2 - D.center‖ :=
    mul_le_of_le_one_left (norm_nonneg _) hs1
  linarith

theorem refl_piecewise (c : ℂ) : PiecewiseC1 (Path.refl c) :=
  piecewiseC1_of_smooth (Path.refl c) (fun _ => c) contDiff_const (fun t => by simp)

end G2037P2Aux

open G2037P2Aux

/-- Index of a gap cycle is zero at every point outside its disc. -/
theorem g2037p2_index_zero_off_disc (D : DiscWithSegment) {z : ℂ}
    (hz : D.radius ≤ dist z D.center) : indexIntegral (gapCycle D) z = 0 := by
  have hzU : z ∉ ball D.center D.radius := fun h => absurd (mem_ball.1 h) (not_lt.2 hz)
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => (w - z)⁻¹) (ball D.center D.radius) := by
    intro w hw
    have hwz : w - z ≠ 0 := sub_ne_zero.2 (fun h => hzU (h ▸ hw))
    exact ((differentiableAt_id.sub_const z).inv hwz).differentiableWithinAt
  have hmain := curveIntegral_eq_of_free_homotopy (gapCycle D) (Path.refl D.center)
    (gapCycle_piecewise D) (refl_piecewise D.center) (ball D.center D.radius) isOpen_ball
    (fun w : ℂ => (w - z)⁻¹) hdiff (contractH D) (contractH_range D)
    (contractH_zero D) (contractH_one D) (contractH_closed D)
  unfold indexIntegral
  rw [hmain, curveIntegral_refl, mul_zero]

/-- The index of a gap cycle at its chord midpoint is one. -/
theorem g2037p2_index_midpoint (D : DiscWithSegment) :
    indexIntegral (gapCycle D) D.midpoint = 1 := by
  unfold indexIntegral
  rw [(reciprocal_gapCycle D).2]
  exact inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])

/-- Existence of the gap disc of cut `k` from an isolating family. -/
theorem g2037p2_gap_disc_exists {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ}
    (hf : IsolatingFamily38 φ C R) (k : ℤ) :
    ∃ D : DiscWithSegment, D.center = C k ∧ D.radius = R k ∧
      D.a = lamMinus φ k ∧ D.b = lamPlus φ k := by
  have hpos : 0 < R k := by
    obtain ⟨c, N, ⟨hR, -⟩, -⟩ := hf
    exact (hR k).1
  exact ⟨⟨C k, R k, hpos, lamMinus φ k, lamPlus φ k, g2037b1_gapSegment_subset_ball hf k⟩,
    rfl, rfl, rfl, rfl⟩

/-- Gap-cycle pattern for cut `k`: index zero on every other cut, index one at a point of cut `k`
(the chord midpoint). The index-one statement on all of cut `k` is NOT claimed here. -/
theorem g2037p2_gap_cycle_pattern {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ}
    (hf : IsolatingFamily38 φ C R) (k : ℤ) (D : DiscWithSegment)
    (hC : D.center = C k) (hR : D.radius = R k) (ha : D.a = lamMinus φ k) (hb : D.b = lamPlus φ k) :
    (∀ j : ℤ, j ≠ k → ∀ z ∈ gapSegment φ j, indexIntegral (gapCycle D) z = 0) ∧
      indexIntegral (gapCycle D) D.midpoint = 1 ∧ D.midpoint ∈ gapSegment φ k := by
  refine ⟨fun j hjk z hz => ?_, g2037p2_index_midpoint D, ?_⟩
  · apply g2037p2_index_zero_off_disc D
    rw [hC, hR]
    by_contra hlt
    push_neg at hlt
    exact G2037B1Aux.balls_disjoint hf (Ne.symm hjk) (mem_ball.2 hlt)
      (g2037b1_gapSegment_subset_ball hf j hz)
  · unfold gapSegment
    rw [← ha, ← hb]
    exact mid_mem_seg D

end
end NlsGge.GKDefinitionDesign
