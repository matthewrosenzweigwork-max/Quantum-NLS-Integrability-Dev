import Mathlib
import NlsGge.Atomic.LIB.LIB079
import NlsGge.ThirdConsultation.G2.G2037P4M4
import NlsGge.Atomic.M.M008Host
import NlsGge.Atomic.M.M008Loops
import NlsGge.Atomic.M.M008EndpointChainBridge
import NlsGge.Atomic.M.M008EndpointPolygonal

section Part0

                                                                                                                                  
                                                                                                                                    
                                                                                                     
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

/-- The cut disc `cutDisc a u r` is star-shaped about `a - u r/2`, hence preconnected. -/
theorem cutDisc_starConvex (a u : ℂ) (hu : ‖u‖ = 1) (r : ℝ) (hr : 0 < r) :
    StarConvex ℝ (a - u * ((r / 2 : ℝ) : ℂ)) (cutDisc a u r) := by
  have hmul := star_mul_self_of_norm hu
  intro z hz α β hα hβ hαβ
  rw [cutDisc_eq_slit a u hu] at hz ⊢
  obtain ⟨hzb, hzs⟩ := hz
  have hqb : a - u * ((r / 2 : ℝ) : ℂ) ∈ ball a r := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, hu, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    linarith
  refine ⟨(convex_ball a r) hqb hzb hα hβ hαβ, ?_⟩
  simp only [Set.mem_preimage] at hzs ⊢
  have hαβ' : (α : ℂ) + β = 1 := by exact_mod_cast hαβ
  have hq : -star u * (a - u * ((r / 2 : ℝ) : ℂ) - a) = ((r / 2 : ℝ) : ℂ) := by
    linear_combination ((r / 2 : ℝ) : ℂ) * hmul
  have hcomb : -star u * (α • (a - u * ((r / 2 : ℝ) : ℂ)) + β • z - a) =
      (α : ℂ) * ((r / 2 : ℝ) : ℂ) + (β : ℂ) * (-star u * (z - a)) := by
    simp only [Complex.real_smul]
    have : -star u * ((α : ℂ) * (a - u * ((r / 2 : ℝ) : ℂ)) + (β : ℂ) * z - a) =
        (α : ℂ) * (-star u * (a - u * ((r / 2 : ℝ) : ℂ) - a)) + (β : ℂ) * (-star u * (z - a)) := by
      linear_combination (-star u * a) * hαβ'
    rw [this, hq]
  rw [hcomb, Complex.mem_slitPlane_iff]
  rw [Complex.mem_slitPlane_iff] at hzs
  have hr2 : 0 < r / 2 := half_pos hr
  rcases hzs with h | h
  · left
    rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re]
    rcases eq_or_lt_of_le hα with h0 | h0
    · have hβ1 : β = 1 := by linarith
      rw [← h0, hβ1]; simpa using h
    · have := mul_pos h0 hr2
      have := mul_nonneg hβ h.le
      linarith
  · rcases eq_or_lt_of_le hβ with h0 | h0
    · left
      have hα1 : α = 1 := by linarith
      rw [← h0, hα1]; simpa using hr2
    · right
      rw [Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul, Complex.ofReal_im]
      simp only [mul_zero, zero_add]
      exact mul_ne_zero h0.ne' h

theorem cutDisc_base_mem (a u : ℂ) (hu : ‖u‖ = 1) (r : ℝ) (hr : 0 < r) :
    a - u * ((r / 2 : ℝ) : ℂ) ∈ cutDisc a u r := by
  have hmul := star_mul_self_of_norm hu
  rw [cutDisc_eq_slit a u hu]
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, hu, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    linarith
  · simp only [Set.mem_preimage]
    have hq : -star u * (a - u * ((r / 2 : ℝ) : ℂ) - a) = ((r / 2 : ℝ) : ℂ) := by
      linear_combination ((r / 2 : ℝ) : ℂ) * hmul
    rw [hq]
    exact Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using half_pos hr))

theorem cutDisc_nonempty (a u : ℂ) (hu : ‖u‖ = 1) (r : ℝ) (hr : 0 < r) :
    (cutDisc a u r).Nonempty := ⟨_, cutDisc_base_mem a u hu r hr⟩

theorem cutDisc_isPreconnected (a u : ℂ) (hu : ‖u‖ = 1) (r : ℝ) (hr : 0 < r) :
    IsPreconnected (cutDisc a u r) :=
  ((cutDisc_starConvex a u hu r hr).isPathConnected (cutDisc_base_mem a u hu r hr)).isConnected.isPreconnected

end
end NlsGge.ThirdConsultation.MContour

end Part0

section Part1

                                                                                                                                   
                                                                                                                            
                                                                                         
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

theorem complexForm_eq_toSpanSingleton (f : ℂ → ℂ) :
    complexForm f = fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w) := by
  funext w; ext c
  simp [complexForm, mul_comm]

/-- Every closed polygonal chain in the cut disc has zero `omega`-period. -/
theorem omega_chain_period_zero (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) {a : ℂ}
    (L : NlsGge.Atomic.ContourChain.Chain a a) (hL : L.trace ⊆ (gapDiscSeg φ hφ n).domain) :
    L.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (omega φ w)) = 0 := by
  set D := gapDiscSeg φ hφ n with hD
  have hf := omega_differentiableOn_domain φ hφ n
  have hI := L.integrable_toSpanSingleton_of_continuousOn hf.continuousOn hL
  rw [NlsGge.Atomic.ContourChain.Chain.integral_eq_curveIntegral hI, ← complexForm_eq_toSpanSingleton]
  obtain ⟨-, -, -, -, hper⟩ := gap_cycle_period D (omega φ) hf L.path
    ⟨chain_path_slit_piecewiseC1 L, fun y hy => hL hy⟩
  rw [hper, gapCycle_omega_zero, mul_zero]

/-- **Primitive.** `omega` has a single-valued primitive on the cut isolating disc. -/
theorem omega_primitive (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    ∃ F : ℂ → ℂ, ∀ z ∈ (gapDiscSeg φ hφ n).domain, HasDerivAt F (omega φ z) z :=
  NlsGge.G2037P4M4.exists_primitive_of_zero_periods (isOpen_domain _)
    (omega_differentiableOn_domain φ hφ n) (domain_polygonal _)
    (fun L hL => omega_chain_period_zero φ hφ n L hL)

/-- A primitive on the cut disc has a limit at an open gap endpoint (`a = D.a`). -/
theorem primitive_limit_left (D : DiscWithSegment) (hne : D.a ≠ D.b) (f F : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f D.domain) (hF : ∀ z ∈ D.domain, HasDerivAt F (f z) z)
    (hbound : HasEndpointBound f D.domain D.a) :
    ∃ ℓ : ℂ, Tendsto F (𝓝[D.domain] D.a) (𝓝 ℓ) := by
  obtain ⟨δ, hδ, P, hPc, hPd⟩ := endpoint_continuous_primitive D f hf D.a (Or.inl rfl) hbound
  obtain ⟨-, -, hu, -⟩ := disc_segment_coordinates D
  have hL : 0 < ‖D.b - D.a‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
  have hclearpos : 0 < D.radius - dist D.a D.center := by
    have := D.contained (left_mem_segment ℝ D.a D.b)
    rw [mem_ball] at this; linarith
  set r : ℝ := min δ (min (‖D.b - D.a‖ / 2) (D.radius - dist D.a D.center)) with hr
  have hrpos : 0 < r := lt_min hδ (lt_min (by linarith) hclearpos)
  have hrδ : r ≤ δ := min_le_left _ _
  have hrlen : r < ‖D.b - D.a‖ :=
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hrclear : r ≤ D.radius - dist D.a D.center :=
    (min_le_right _ _).trans (min_le_right _ _)
  have heq := endpoint_cutDisc_eq D hne r hrpos hrlen hrclear
  set W : Set ℂ := D.domain ∩ ball D.a r with hW
  have hWo : IsOpen W := by rw [heq]; exact isOpen_cutDisc _ _ hu _
  have hWc : IsPreconnected W := by rw [heq]; exact cutDisc_isPreconnected _ _ hu _ hrpos
  obtain ⟨y0, hy0⟩ : W.Nonempty := by rw [heq]; exact cutDisc_nonempty _ _ hu _ hrpos
  have hWsub : W ⊆ D.domain ∩ ball D.a δ := fun z hz =>
    ⟨hz.1, ball_subset_ball hrδ hz.2⟩
  have hd : ∀ z ∈ W, HasDerivAt (fun y => F y - P y) 0 z := by
    intro z hz
    have := (hF z hz.1).sub (hPd z (hWsub hz))
    rw [sub_self] at this
    exact this
  have hconst : ∀ z ∈ W, F z - P z = F y0 - P y0 := by
    intro z hz
    refine hWo.is_const_of_deriv_eq_zero hWc (f := fun y => F y - P y) ?_ ?_ hz hy0
    · exact fun y hy => (hd y hy).differentiableAt.differentiableWithinAt
    · intro y hy; exact (hd y hy).deriv
  refine ⟨P D.a + (F y0 - P y0), ?_⟩
  have hWmem : W ∈ 𝓝[D.domain] D.a := by
    rw [hW]
    exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hrpos))
  have hPt : Tendsto P (𝓝[W] D.a) (𝓝 (P D.a)) := by
    have h1 := (hPc D.a (Or.inr rfl)).tendsto
    refine h1.mono_left (nhdsWithin_mono _ ?_)
    intro z hz; exact Or.inl (hWsub hz)
  have hnh : 𝓝[W] D.a = 𝓝[D.domain] D.a := by
    rw [hW, inter_comm]
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hrpos))
  rw [← hnh]
  refine (hPt.add_const (F y0 - P y0)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have := hconst z hz
  linear_combination -this

/-- A primitive on the cut disc has a limit at either endpoint. -/
theorem primitive_limit (D : DiscWithSegment) (hne : D.a ≠ D.b) (f F : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f D.domain) (hF : ∀ z ∈ D.domain, HasDerivAt F (f z) z)
    (a : ℂ) (ha : a = D.a ∨ a = D.b) (hbound : HasEndpointBound f D.domain a) :
    ∃ ℓ : ℂ, Tendsto F (𝓝[D.domain] a) (𝓝 ℓ) := by
  rcases ha with rfl | rfl
  · exact primitive_limit_left D hne f F hf hF hbound
  · have hdom := D.swap_domain
    have := primitive_limit_left D.swap hne.symm f F (by rw [hdom]; exact hf)
      (by rw [hdom]; exact hF) (by rw [hdom]; exact hbound)
    rw [hdom] at this
    exact this

end
end NlsGge.ThirdConsultation.MContour

end Part1

