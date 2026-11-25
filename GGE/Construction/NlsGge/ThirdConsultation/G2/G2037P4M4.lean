import Mathlib
import NlsGge.Atomic.Support.ContourPolygon

                                                                                    
                                                                                                   
                                                                                               
                                                                   
                                                                                                   
                                                                                                       

set_option autoImplicit false

open Set Metric Relation

namespace NlsGge.G2037P4M4
noncomputable section

open NlsGge.Atomic.ContourChain

/-- A straight leaf chain stays in `U` when its segment does. -/
theorem lineChain_trace_subset {a b : ℂ} {U : Set ℂ} (h : segment ℝ a b ⊆ U) :
    (NlsGge.Atomic.ContourPolygon.lineChain a b).trace ⊆ U := by
  rintro _ ⟨t, rfl⟩
  apply h
  rw [segment_eq_image_lineMap]
  exact ⟨(t : ℝ), t.2, by simp [Path.segment_apply]⟩

/-- Reachability: points of `U` are endpoints of chains of segments inside `U` from `z0`. -/
theorem exists_chain_in {U : Set ℂ} {z0 : ℂ} (hz0 : z0 ∈ U) {z : ℂ}
    (h : ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ U) z0 z) :
    ∃ c : Chain z0 z, c.trace ⊆ U := by
  induction h with
  | refl =>
      refine ⟨NlsGge.Atomic.ContourPolygon.lineChain z0 z0, lineChain_trace_subset ?_⟩
      rw [segment_same]
      exact singleton_subset_iff.2 hz0
  | tail _ hbc ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨Chain.join c (NlsGge.Atomic.ContourPolygon.lineChain _ _), ?_⟩
      rw [Chain.trace_join]
      exact union_subset hc (lineChain_trace_subset hbc)

/-- Path independence from vanishing closed-chain periods. -/
theorem chain_integral_eq {U : Set ℂ} {f : ℂ → ℂ} (hfc : ContinuousOn f U)
    (hper : ∀ {a : ℂ} (L : Chain a a), L.trace ⊆ U →
      L.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) = 0)
    {z0 z : ℂ} (c1 c2 : Chain z0 z) (h1 : c1.trace ⊆ U) (h2 : c2.trace ⊆ U) :
    c1.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) =
      c2.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) := by
  have hL : (Chain.join c1 c2.reverse).trace ⊆ U := by
    rw [Chain.trace_join, Chain.trace_reverse]
    exact union_subset h1 h2
  have h0 := hper (Chain.join c1 c2.reverse) hL
  have hi2 := c2.integrable_toSpanSingleton_of_continuousOn hfc h2
  have h0' : c1.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) +
      c2.reverse.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) = 0 := h0
  rw [Chain.integral_reverse hi2] at h0'
  linear_combination h0'

/-- **M4.** A holomorphic function on a polygonally connected open set with vanishing closed-chain
periods has a primitive on that set. -/
theorem exists_primitive_of_zero_periods {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U)
    (hconn : ∀ z ∈ U, ∀ w ∈ U, ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ U) z w)
    (hper : ∀ {a : ℂ} (L : Chain a a), L.trace ⊆ U →
      L.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) = 0) :
    ∃ F : ℂ → ℂ, ∀ z ∈ U, HasDerivAt F (f z) z := by
  classical
  by_cases hne : U.Nonempty
  swap
  · refine ⟨fun _ => 0, fun z hz => absurd ⟨z, hz⟩ hne⟩
  obtain ⟨z0, hz0⟩ := hne
  have hfc : ContinuousOn f U := hf.continuousOn
  have hreach : ∀ z ∈ U, ∃ c : Chain z0 z, c.trace ⊆ U := fun z hz =>
    exists_chain_in hz0 (hconn z0 hz0 z hz)
  let F : ℂ → ℂ := fun z =>
    if h : ∃ c : Chain z0 z, c.trace ⊆ U then
      (Classical.choose h).integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w))
    else 0
  have hF : ∀ z : ℂ, ∀ c : Chain z0 z, c.trace ⊆ U →
      F z = c.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) := by
    intro z c hc
    have hex : ∃ c : Chain z0 z, c.trace ⊆ U := ⟨c, hc⟩
    have hsp := Classical.choose_spec hex
    show (if h : ∃ c : Chain z0 z, c.trace ⊆ U then
      (Classical.choose h).integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w))
      else 0) = _
    rw [dif_pos hex]
    exact chain_integral_eq hfc hper _ c hsp hc
  refine ⟨F, fun z hz => ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hz
  obtain ⟨P, hP⟩ := (hf.mono hball).isExactOn_ball
  obtain ⟨cz, hcz⟩ := hreach z hz
  have hFloc : ∀ w ∈ ball z r, F w = P w + (F z - P z) := by
    intro w hw
    have hseg : segment ℝ z w ⊆ ball z r :=
      (convex_ball z r).segment_subset (mem_ball_self hr) hw
    have hsegU : segment ℝ z w ⊆ U := hseg.trans hball
    have hcw : (Chain.join cz (NlsGge.Atomic.ContourPolygon.lineChain z w)).trace ⊆ U := by
      rw [Chain.trace_join]
      exact union_subset hcz (lineChain_trace_subset hsegU)
    have hFw := hF w _ hcw
    have hfball : ContinuousOn f (ball z r) := hfc.mono hball
    have htr : (NlsGge.Atomic.ContourPolygon.lineChain z w).trace ⊆ ball z r :=
      lineChain_trace_subset hseg
    obtain ⟨-, hlin⟩ := (NlsGge.Atomic.ContourPolygon.lineChain z w).integral_eq_sub_of_hasDerivAt
      hfball (fun y hy => hP y hy) htr
    have hFz := hF z cz hcz
    rw [hFw]
    show cz.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) +
      (NlsGge.Atomic.ContourPolygon.lineChain z w).integral
        (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) = _
    rw [hlin, ← hFz]
    ring
  have hPz : HasDerivAt P (f z) z := hP z (mem_ball_self hr)
  have hev : (fun y => P y + (F z - P z)) =ᶠ[nhds z] F := by
    filter_upwards [ball_mem_nhds z hr] with y hy
    exact (hFloc y hy).symm
  exact (hPz.add_const (F z - P z)).congr_of_eventuallyEq hev.symm

end
end NlsGge.G2037P4M4
