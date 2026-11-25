import Mathlib
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.XiSqPeriod
import NlsGge.Atomic.LIB.LIB079
import NlsGge.Atomic.M.M008Host
import NlsGge.Atomic.M.M008Loops
import NlsGge.Atomic.M.M008Collapsed
import NlsGge.Atomic.M.M008EndpointConst
import NlsGge.Atomic.M.M008EndpointZero

                                                                                                                          
                                                                                                                                 
                                                                                                                         
                                                                       
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

/-- Collapsed gap: every admissible endpoint curve has joint improper integral zero. -/
theorem omega_endpointIntegral_collapsed (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hgap : lamMinus φ n = lamPlus φ n) :
    ∀ p : ℝ → ℂ, AdmissibleEndpointCurve φ n p → HasEndpointIntegral φ p 0 := by
  intro p hp
  obtain ⟨hpc, hpd, h0, h1, hcase⟩ := hp
  set D := gapDiscSeg φ hφ n with hD
  have hf : DifferentiableOn ℂ (omega φ) D.domain := omega_differentiableOn_domain φ hφ n
  have hdom : D.domain = discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n) := rfl
  rcases hcase with hmem | ⟨-, hconst⟩
  · obtain ⟨f, hfan, hfeq⟩ := omega_extends_collapsed_complex φ hφ n hgap.symm
    obtain ⟨Fc, hFc⟩ := (convex_ball (discC φ n) (discR φ n)).exists_forall_hasDerivWithinAt
      hfan.differentiableOn
    have hFU : ∀ z ∈ D.domain, HasDerivAt Fc (omega φ z) z := by
      intro z hz
      rw [hdom] at hz
      have hzne : z ≠ lamMinus φ n := fun h => hz.2 (h ▸ left_mem_segment ℝ _ _)
      have := (hFc z hz.1).hasDerivAt (isOpen_ball.mem_nhds hz.1)
      rwa [hfeq z hz.1 hzne] at this
    have he : lamMinus φ n ∈ discU φ n := own_segment_subset_disc φ hφ n (left_mem_segment ℝ _ _)
    have hFcc : ContinuousAt Fc (lamMinus φ n) :=
      ((hFc _ he).hasDerivAt (isOpen_ball.mem_nhds he)).continuousAt
    have h := endpointIntegral_of_primitive φ D.domain hf.continuousOn Fc hFU p hpc hpd
      (fun t ht => by rw [hdom]; exact hmem t ht) (Fc (lamMinus φ n)) (Fc (lamMinus φ n))
      (by rw [h0]; exact hFcc.tendsto.mono_left nhdsWithin_le_nhds)
      (by rw [h1, ← hgap]; exact hFcc.tendsto.mono_left nhdsWithin_le_nhds)
    rwa [sub_self] at h
  · have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, deriv p t = 0 := by
      intro t ht
      have hev : p =ᶠ[𝓝 t] fun _ => lamMinus φ n := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        exact hconst s (Ioo_subset_Icc_self hs)
      rw [hev.deriv_eq]; simp
    have hzero : ∀ t ∈ Ioo (0 : ℝ) 1, omega φ (p t) * deriv p t = 0 := fun t ht => by
      rw [hderiv t ht, mul_zero]
    have hIcc : ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 → Icc ε (1 - η) ⊆ Ioo (0 : ℝ) 1 := by
      intro ε η hε hη hεη t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hint : ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 →
        IntervalIntegrable (fun t : ℝ => omega φ (p t) * deriv p t) volume ε (1 - η) := by
      intro ε η hε hη hεη
      have hle : ε ≤ 1 - η := by linarith
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hle]
      exact (continuousOn_const (c := (0 : ℂ))).congr (fun t ht => hzero t (hIcc ε η hε hη hεη ht))
    refine ⟨hint, ?_⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    have hle : q.1 ≤ 1 - q.2 := by linarith
    have : ∫ t in q.1..(1 - q.2), omega φ (p t) * deriv p t = ∫ t in q.1..(1 - q.2), (0 : ℂ) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [uIcc_of_le hle] at ht
      exact hzero t (hIcc q.1 q.2 hq1 hq2 hq3 ht)
    rw [this]; simp

/-- Open gap: the primitive of `omega` on the cut disc has the SAME limit at both gap endpoints (the content of
conjunct (4), in primitive form; used for finite endpoint chains). -/
theorem omega_primitive_common_limit (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hne : lamMinus φ n ≠ lamPlus φ n) :
    ∃ F : ℂ → ℂ, (∀ z ∈ (gapDiscSeg φ hφ n).domain, HasDerivAt F (omega φ z) z) ∧
      ∃ ℓ : ℂ, Tendsto F (𝓝[(gapDiscSeg φ hφ n).domain] (lamMinus φ n)) (𝓝 ℓ) ∧
        Tendsto F (𝓝[(gapDiscSeg φ hφ n).domain] (lamPlus φ n)) (𝓝 ℓ) := by
  set D := gapDiscSeg φ hφ n with hD
  have hf : DifferentiableOn ℂ (omega φ) D.domain := omega_differentiableOn_domain φ hφ n
  have hdom : D.domain = discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n) := rfl
  obtain ⟨F, lm, lp, hF, hlm, hlp⟩ := omega_primitive_limits φ hφ n hne
  obtain ⟨p0, hp0, hp00⟩ := omega_explicit_curve_zero φ hφ n hne
  obtain ⟨hpc, hpd, h0, h1, hcase⟩ := hp0
  have hmem : ∀ t ∈ Ioo (0 : ℝ) 1, p0 t ∈ D.domain := by
    rcases hcase with h | ⟨h, -⟩
    · intro t ht; rw [hdom]; exact h t ht
    · exact absurd h hne
  have h := endpointIntegral_of_primitive φ D.domain hf.continuousOn F hF p0 hpc hpd hmem lm lp
    (by rw [h0]; exact hlm) (by rw [h1]; exact hlp)
  have hlpm : lp - lm = 0 := HasEndpointIntegral.unique h hp00
  have hlpeq : lp = lm := sub_eq_zero.1 hlpm
  exact ⟨F, hF, lm, hlm, by rw [← hlpeq]; exact hlp⟩

/-- **Conjunct (4) of the section-10E head.** -/
theorem omega_endpointCurve_zero (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    ∀ p : ℝ → ℂ, AdmissibleEndpointCurve φ n p → HasEndpointIntegral φ p 0 := by
  by_cases hne : lamMinus φ n = lamPlus φ n
  · exact omega_endpointIntegral_collapsed φ hφ n hne
  · intro p hp
    obtain ⟨E, hE⟩ := omega_endpointIntegral_const φ hφ n hne
    obtain ⟨p0, hp0, hp00⟩ := omega_explicit_curve_zero φ hφ n hne
    have hE0 : E = 0 := HasEndpointIntegral.unique (hE p0 hp0) hp00
    rw [← hE0]
    exact hE p hp

end
end NlsGge.ThirdConsultation.MContour
