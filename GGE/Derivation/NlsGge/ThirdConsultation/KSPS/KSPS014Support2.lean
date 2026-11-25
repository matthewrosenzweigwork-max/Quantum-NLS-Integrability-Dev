import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS014Host
import NlsGge.ThirdConsultation.KSPS.IBP002Support
import NlsGge.ThirdConsultation.G1.IBP038Support
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.KSPSSupport.CORE01

/- KSPS-014 SUPPORT2 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS014Support2.lean.
   The H^1 trace leaf of KSPS-014 (Pro round 14, "Mandatory interpretation": coefficientTraceZero is
   f(0) = int_0^1 [f - (1-t) f'], and coefficientTrace is the continuous representative on [0,1]):
   * h1_trace_ae: for f in H^1, cover f = T0(f) + int_0^x cover f' for a.e. x in (0,1], where
     T0(f) = int_0^1 [cover f - (1-t) cover f'] (the continuous H^1 representative c of NlsGge.Analysis, its
     primitive identity, and one integration by parts against 1-t give c(0) = T0(f));
   * coefficientTrace_ae / coefficientTrace_continuousOn for 1 <= k <= N (coefficients are H^1 there). -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.Schur NlsGge.Analysis
open NlsGge.ThirdConsultation.KSPS

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

theorem uA_deriv_eq_weakDerivative (f : PhysicalL2) (hf : physicalSobolev 1 f) :
    uA_deriv f ((physicalSobolev_iff_ordinary 1 f).1 hf) = weakDerivative f := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply, uA_deriv_fourier,
    physicalFourier_weakDerivative f hf n]
  rfl

theorem h1_trace_ae (f : PhysicalL2) (hf : physicalSobolev 1 f) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 →
      coverRep38 f x =
        (∫ t in (0 : ℝ)..1, coverRep38 f t - ((1 - t : ℝ) : ℂ) * coverRep38 (weakDerivative f) t) +
          ∫ t in (0 : ℝ)..x, coverRep38 (weakDerivative f) t := by
  have hu := (physicalSobolev_iff_ordinary 1 f).1 hf
  set c : ℝ → ℂ := fun t => physicalH1Continuous f hu (t : PhysicalCircle) with hcdef
  set g : ℝ → ℂ := coverRep38 (weakDerivative f) with hgdef
  have hg : IntervalIntegrable g volume 0 1 := intervalIntegrable_coverRep38_one _
  -- primitive identity of the continuous representative
  have hS : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      (actualPhysicalL2SourcePotential (weakDerivative f) : ℝ → ℂ) s = g s := by
    filter_upwards [actualPhysicalL2SourcePotential_ae (weakDerivative f),
      MeasureTheory.ae_restrict_of_ae (coverRep38_ae_phys (weakDerivative f))] with s h1 h2
    rw [h1, hgdef, h2]
  have hprim : ∀ t ∈ Set.Icc (0 : ℝ) 1, c t = c 0 + ∫ s in (0 : ℝ)..t, g s := by
    intro t ht
    have h := uA_integral_deriv f hu t ht
    rw [uA_deriv_eq_weakDerivative f hf] at h
    have h' : ∫ s in (0 : ℝ)..t, (actualPhysicalL2SourcePotential (weakDerivative f) : ℝ → ℂ) s =
        ∫ s in (0 : ℝ)..t, g s := by
      refine intervalIntegral.integral_congr_ae ?_
      have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ioc (0 : ℝ) 1 := Set.Ioc_subset_Ioc le_rfl ht.2
      have := (ae_restrict_iff' measurableSet_Ioc).mp hS
      filter_upwards [this] with s hs hmem
      rw [Set.uIoc_of_le ht.1] at hmem
      exact hs (hsub hmem)
    rw [h'] at h
    simp only [hcdef]
    rw [h]; ring
  have hprim1 : ∀ t ∈ Set.uIcc (0 : ℝ) 1, c t = c 0 + ∫ s in (0 : ℝ)..t, g s := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact hprim t ht
  have hAC : AbsolutelyContinuousOnInterval c 0 1 := by
    have hp := NlsGge.SpectralFoundations.complex_intervalIntegral_primitive_absolutelyContinuousV2
      hg (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1)
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c 0) 0 1 :=
      (contDiffOn_const (c := c 0) (n := 1) (s := Set.uIcc (0 : ℝ) 1)).absolutelyContinuousOnInterval
    exact (hc.add hp).congr (fun t ht => (hprim1 t ht).symm)
  have hder : ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 → HasDerivAt c (g t) t := by
    have h0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by simp [ae_iff, measure_singleton]
    have h1 : ∀ᵐ y : ℝ ∂volume, y ≠ 1 := by simp [ae_iff, measure_singleton]
    filter_upwards [hg.ae_hasDerivAt_integral, h0, h1] with y hy hy0 hy1 hmem
    have hd := (hy hmem 0 (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1)).const_add (c 0)
    refine hd.congr_of_eventuallyEq ?_
    rw [Set.uIcc_of_le zero_le_one] at hmem
    have hmem' : y ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hmem.1 (Ne.symm hy0), lt_of_le_of_ne hmem.2 hy1⟩
    filter_upwards [Ioo_mem_nhds hmem'.1 hmem'.2] with z hz
    exact hprim1 z (by rw [Set.uIcc_of_le zero_le_one]; exact ⟨hz.1.le, hz.2.le⟩)
  -- c = cover f a.e. on (0,1]
  have hc_ae : ∀ᵐ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 → c x = coverRep38 f x :=
    (ae_restrict_iff' measurableSet_Ioc).mp (uA_continuous_rep_ae f hu)
  -- integration by parts against 1 - t
  have hψ : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ)) (-1) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (1 : ℂ) - (s : ℂ)) (0 - 1) t :=
      (hasDerivAt_const t (1 : ℂ)).sub (Complex.ofRealCLM.hasDerivAt (x := t))
    simpa using h1
  have hψint : IntervalIntegrable (fun _ : ℝ => (-1 : ℂ)) volume 0 1 := intervalIntegrable_const
  have hibp := NlsGge.SpectralFoundations.complex_ac_pointwise_test_integration_by_parts
    hAC hg hder hψ hψint
  simp only [sub_self, Complex.ofReal_zero, mul_zero, sub_zero, Complex.ofReal_one, mul_one,
    zero_sub] at hibp
  have hcint : IntervalIntegrable c volume 0 1 :=
    (hAC.continuousOn).intervalIntegrable
  have hgψint : IntervalIntegrable (fun t : ℝ => ((1 - t : ℝ) : ℂ) * g t) volume 0 1 :=
    hg.continuousOn_mul (by fun_prop)
  have hT0 : (∫ t in (0 : ℝ)..1, coverRep38 f t - ((1 - t : ℝ) : ℂ) * g t) = c 0 := by
    have e1 : (∫ t in (0 : ℝ)..1, coverRep38 f t - ((1 - t : ℝ) : ℂ) * g t) =
        ∫ t in (0 : ℝ)..1, c t - ((1 - t : ℝ) : ℂ) * g t := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hc_ae] with t ht hmem
      rw [Set.uIoc_of_le zero_le_one] at hmem
      rw [ht hmem]
    rw [e1, intervalIntegral.integral_sub hcint hgψint]
    have e2 : (∫ t in (0 : ℝ)..1, c t * (-1 : ℂ)) = -∫ t in (0 : ℝ)..1, c t := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      ring
    have e3 : (∫ t in (0 : ℝ)..1, g t * ((1 - t : ℝ) : ℂ)) =
        ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) * g t := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      ring
    rw [e2, e3] at hibp
    linear_combination (-1 : ℂ) * hibp
  filter_upwards [hc_ae] with x hx hmem
  rw [← hx hmem, hT0]
  exact hprim x ⟨hmem.1.le, hmem.2⟩

theorem coefficientTrace_ae {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (k : ℕ)
    (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 →
      coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b k) x =
        coefficientTrace φ b k x := by
  have hf := NlsGge.ThirdConsultation.KSPSSupport.h150_coef_H1 N hN φ b k hk1 hkN
  filter_upwards [h1_trace_ae _ hf] with x hx hmem
  rw [hx hmem]
  rfl

theorem coefficientTrace_continuousOn {N : ℕ} (φ : SobolevC N) (b : Bool) (k : ℕ) :
    ContinuousOn (coefficientTrace φ b k) (Set.Icc (0 : ℝ) 1) := by
  have hg := intervalIntegrable_coverRep38_one
    (weakDerivative (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b k))
  have hg' : IntegrableOn
      (coverRep38 (weakDerivative (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b k)))
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 hg
  have hp := intervalIntegral.continuousOn_primitive_interval hg'
  rw [Set.uIcc_of_le zero_le_one] at hp
  show ContinuousOn (fun x : ℝ => coefficientTraceZero φ b k + ∫ t in (0 : ℝ)..x,
    coverRep38 (weakDerivative (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b k)) t) _
  exact continuousOn_const.add hp

end
end NlsGge.ThirdConsultation.KSPSWKB
