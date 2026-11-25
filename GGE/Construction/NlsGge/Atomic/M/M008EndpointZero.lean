import Mathlib
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.XiSqPeriod
import NlsGge.Atomic.LIB.LIB079
import NlsGge.Atomic.M.M008Host
import NlsGge.Atomic.M.M008Loops
import NlsGge.Atomic.M.M008EndpointBound
import NlsGge.Atomic.M.M008EndpointConst
import NlsGge.Atomic.M.M008EndpointJouk

                                                                                                                               
                                      
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

/-- Integrability of the integrand on compact subintervals of the open parameter interval. -/
theorem endpoint_integrand_integrable (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (p : ℝ → ℂ)
    (hpc : ContinuousOn p (Icc (0 : ℝ) 1)) (hpd : ContDiffOn ℝ 1 p (Ioo (0 : ℝ) 1))
    (hmem : ∀ t ∈ Ioo (0 : ℝ) 1, p t ∈ (gapDiscSeg φ hφ n).domain) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 →
      IntervalIntegrable (fun t : ℝ => omega φ (p t) * deriv p t) volume ε (1 - η) := by
  intro ε η hε hη hεη
  have hf := omega_differentiableOn_domain φ hφ n
  have hderiv_cont : ContinuousOn (deriv p) (Ioo (0 : ℝ) 1) :=
    hpd.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hωp : ContinuousOn (fun t => omega φ (p t)) (Ioo (0 : ℝ) 1) :=
    hf.continuousOn.comp (hpc.mono Ioo_subset_Icc_self) hmem
  have hle : ε ≤ 1 - η := by linarith
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
  refine (ContinuousOn.mul hωp hderiv_cont).mono ?_ |>.integrableOn_Icc
  intro t ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem omega_explicit_curve_zero (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hne : lamMinus φ n ≠ lamPlus φ n) :
    ∃ p : ℝ → ℂ, AdmissibleEndpointCurve φ n p ∧ HasEndpointIntegral φ p 0 := by
  obtain ⟨δ0, hδ0, hball⟩ := jouk_ball_nbhd φ hφ n
  obtain ⟨σ, hσ2, hσ⟩ := rootFactor_jouk_sign φ hφ n hne hδ0 hball
  obtain ⟨b, hb⟩ := Bj_primitive φ hφ n hball
  have hbsym := primitive_symm φ hφ n hne hδ0 hball hσ2 hσ hb
  have hpi := Real.pi_pos
  set δ : ℝ := δ0 / 2 with hδ
  have hδpos : 0 < δ := half_pos hδ0
  have hδlt : δ < δ0 := by rw [hδ]; linarith
  set v : ℝ → ℂ := fun t => ((δ * Real.sin (Real.pi * t) : ℝ) : ℂ) +
    ((Real.pi * t : ℝ) : ℂ) * Complex.I with hv
  have hvcd : ContDiff ℝ 1 v := by
    have hre : ContDiff ℝ 1 (fun t : ℝ => ((δ * Real.sin (Real.pi * t) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)))
    have him : ContDiff ℝ 1 (fun t : ℝ => ((Real.pi * t : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
    exact hre.add (him.mul contDiff_const)
  have hvd : ∀ t, HasDerivAt v (deriv v t) t := fun t =>
    (hvcd.differentiable (by norm_num) t).hasDerivAt
  have hvre : ∀ t, (v t).re = δ * Real.sin (Real.pi * t) := fun t => ofReal_add_mul_I_re _ _
  have hvim : ∀ t, (v t).im = Real.pi * t := fun t => ofReal_add_mul_I_im _ _
  have hvIcc : ∀ t ∈ Icc (0 : ℝ) 1, v t ∈ Rfull δ0 := by
    intro t ht
    have hs1 := Real.sin_le_one (Real.pi * t)
    have hs2 := Real.neg_one_le_sin (Real.pi * t)
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · show -δ0 < (v t).re; rw [hvre]; nlinarith
    · show (v t).re < δ0; rw [hvre]; nlinarith
    · show -1 < (v t).im; rw [hvim]; nlinarith [ht.1]
    · show (v t).im < 2 * Real.pi + 1; rw [hvim]; nlinarith [ht.2]
  have hvIoo : ∀ t ∈ Ioo (0 : ℝ) 1, v t ∈ Rpos δ0 := by
    intro t ht
    have hs1 := Real.sin_le_one (Real.pi * t)
    have hs0 : 0 < Real.sin (Real.pi * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith [ht.1]) (by nlinarith [ht.2])
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · show 0 < (v t).re; rw [hvre]; positivity
    · show (v t).re < δ0; rw [hvre]; nlinarith
    · show -1 < (v t).im; rw [hvim]; nlinarith [ht.1]
    · show (v t).im < 2 * Real.pi + 1; rw [hvim]; nlinarith [ht.2]
  set p : ℝ → ℂ := fun t => jouk (gapMid φ n) (gapHalf φ n) (v t) with hp
  have hpcd : ContDiff ℝ 1 p := by
    simp only [hp, jouk]
    exact contDiff_const.sub (contDiff_const.mul ((Complex.contDiff_cosh.restrict_scalars ℝ).comp hvcd))
  have hdom : ∀ t ∈ Ioo (0 : ℝ) 1,
      p t ∈ discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n) := fun t ht =>
    jouk_mem_domain φ hφ n hne hδ0 hball (hvIoo t ht)
  have hp0 : p 0 = lamMinus φ n := by
    have : v 0 = 0 := by simp [hv]
    simp only [hp, this, jouk, Complex.cosh_zero, mul_one]
    rw [lamMinus_eq]
  have hp1 : p 1 = lamPlus φ n := by
    have : v 1 = ((Real.pi : ℝ) : ℂ) * Complex.I := by simp [hv]
    simp only [hp, this, jouk]
    rw [Complex.cosh_mul_I, ← Complex.ofReal_cos, Real.cos_pi, lamPlus_eq]
    push_cast; ring
  refine ⟨p, ⟨hpcd.continuous.continuousOn, hpcd.contDiffOn, hp0, hp1, Or.inl hdom⟩, ?_⟩
  have hdom' : ∀ t ∈ Ioo (0 : ℝ) 1, p t ∈ (gapDiscSeg φ hφ n).domain := hdom
  refine ⟨endpoint_integrand_integrable φ hφ n p hpcd.continuous.continuousOn hpcd.contDiffOn hdom', ?_⟩
  -- the integral on `[ε, 1-η]` in terms of the primitive `b`
  have hIcc : ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 → Icc ε (1 - η) ⊆ Ioo (0 : ℝ) 1 := by
    intro ε η hε hη hεη t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hint : ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 →
      ∫ t in ε..(1 - η), omega φ (p t) * deriv p t = -σ * (b (v (1 - η)) - b (v ε)) := by
    intro ε η hε hη hεη
    have hle : ε ≤ 1 - η := by linarith
    have hsub := hIcc ε η hε hη hεη
    have hcongr : ∫ t in ε..(1 - η), omega φ (p t) * deriv p t =
        ∫ t in ε..(1 - η), (-σ) * (Bj φ n (v t) * deriv v t) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [uIcc_of_le hle] at ht
      exact omega_jouk_curve_integrand φ hφ n hne hδ0 hball hσ2 hσ v (deriv v t) t (hvd t)
        (hvIoo t (hsub ht))
    rw [hcongr, intervalIntegral.integral_const_mul]
    have hBcont : ContinuousOn (fun t : ℝ => Bj φ n (v t) * deriv v t) (uIcc ε (1 - η)) := by
      rw [uIcc_of_le hle]
      refine ContinuousOn.mul ?_ (hvcd.continuous_deriv le_rfl).continuousOn
      refine (Bj_differentiableOn φ hφ n hball).continuousOn.comp hvcd.continuous.continuousOn ?_
      intro t ht
      exact hvIcc t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hftc : ∫ t in ε..(1 - η), Bj φ n (v t) * deriv v t = b (v (1 - η)) - b (v ε) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => b (v t)) (fun t ht => ?_)
        hBcont.intervalIntegrable
      rw [uIcc_of_le hle] at ht
      have h := (hb (v t) (hvIcc t ⟨by linarith [ht.1], by linarith [ht.2]⟩)).scomp t (hvd t)
      simp only [smul_eq_mul] at h
      exact h.congr_deriv (mul_comm _ _)
    rw [hftc]
  -- limits
  have hbv : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun s => b (v s)) t := by
    intro t ht
    exact ((hb (v t) (hvIcc t ht)).continuousAt).comp (hvcd.continuous.continuousAt)
  have hv0 : v 0 = 0 := by simp [hv]
  have hv1 : v 1 = ((Real.pi : ℝ) : ℂ) * Complex.I := by simp [hv]
  have hlim1 : Tendsto (fun q : ℝ × ℝ => b (v (1 - q.2))) (𝓝[endpointRegion] ((0 : ℝ), (0 : ℝ)))
      (𝓝 (b (v 1))) := by
    have hq : Tendsto (fun q : ℝ × ℝ => 1 - q.2) (𝓝[endpointRegion] ((0 : ℝ), (0 : ℝ))) (𝓝 1) := by
      have : Tendsto (fun q : ℝ × ℝ => 1 - q.2) (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 (1 - (0 : ℝ))) :=
        (continuous_const.sub continuous_snd).tendsto ((0 : ℝ), (0 : ℝ))
      simpa using this.mono_left (nhdsWithin_le_nhds (s := endpointRegion))
    exact (hbv 1 ⟨zero_le_one, le_refl _⟩).tendsto.comp hq
  have hlim0 : Tendsto (fun q : ℝ × ℝ => b (v q.1)) (𝓝[endpointRegion] ((0 : ℝ), (0 : ℝ)))
      (𝓝 (b (v 0))) := by
    have hq : Tendsto (fun q : ℝ × ℝ => q.1) (𝓝[endpointRegion] ((0 : ℝ), (0 : ℝ))) (𝓝 0) :=
      (continuous_fst.tendsto ((0 : ℝ), (0 : ℝ))).mono_left nhdsWithin_le_nhds
    exact (hbv 0 ⟨le_refl _, zero_le_one⟩).tendsto.comp hq
  have hlim := (hlim1.sub hlim0).const_mul (-σ)
  have hval : -σ * (b (v 1) - b (v 0)) = 0 := by
    rw [hv0, hv1, hbsym]; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (hint q.1 q.2 hq.1 hq.2.1 hq.2.2).symm

end
end NlsGge.ThirdConsultation.MContour
