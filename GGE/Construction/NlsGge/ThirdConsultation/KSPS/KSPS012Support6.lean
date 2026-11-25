import Mathlib
import NlsGge.ThirdConsultation.KSPS.IBP002Support
import NlsGge.ThirdConsultation.KSPS.KSPS011Support9
import NlsGge.ThirdConsultation.KSPS.KSPS012Support5

                                                                                                                    
                                                                                                                 
                            
                                                                                                                             
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem ibp_tail (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (ν : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ν * ∫ s in t..1, Complex.exp (ν * (s : ℂ)) * coverRep38 (physicalSobolevEmbed 1 u) s =
      Complex.exp (ν * ((1 : ℝ) : ℂ)) * sobolevPointValue 1 u 1 -
        Complex.exp (ν * (t : ℂ)) * sobolevPointValue 1 u t -
        ∫ s in t..1, Complex.exp (ν * (s : ℂ)) * coverRep38 (physicalSobolevDerivative38 1 u) s := by
  have hfc : Continuous fun s : ℝ => Complex.exp (ν * (s : ℂ)) := by fun_prop
  have hf1 : IntervalIntegrable (fun s : ℝ => Complex.exp (ν * (s : ℂ)) *
      coverRep38 (physicalSobolevEmbed 1 u) s) volume 0 1 :=
    (intervalIntegrable_coverRep38_one _).continuousOn_mul hfc.continuousOn
  have hg1 : IntervalIntegrable (fun s : ℝ => Complex.exp (ν * (s : ℂ)) *
      coverRep38 (physicalSobolevDerivative38 1 u) s) volume 0 1 :=
    (intervalIntegrable_coverRep38_one _).continuousOn_mul hfc.continuousOn
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl ht.2
  have hI : ∫ s in t..1, Complex.exp (ν * (s : ℂ)) * coverRep38 (physicalSobolevEmbed 1 u) s =
      (∫ s in (0 : ℝ)..1, Complex.exp (ν * (s : ℂ)) * coverRep38 (physicalSobolevEmbed 1 u) s) -
        ∫ s in (0 : ℝ)..t, Complex.exp (ν * (s : ℂ)) * coverRep38 (physicalSobolevEmbed 1 u) s :=
    (intervalIntegral.integral_interval_sub_left hf1 (hf1.mono_set hsub)).symm
  have hD : ∫ s in t..1, Complex.exp (ν * (s : ℂ)) * coverRep38 (physicalSobolevDerivative38 1 u) s =
      (∫ s in (0 : ℝ)..1, Complex.exp (ν * (s : ℂ)) * coverRep38 (physicalSobolevDerivative38 1 u) s) -
        ∫ s in (0 : ℝ)..t, Complex.exp (ν * (s : ℂ)) * coverRep38 (physicalSobolevDerivative38 1 u) s :=
    (intervalIntegral.integral_interval_sub_left hg1 (hg1.mono_set hsub)).symm
  have h1 := NlsGge.ThirdConsultation.KSPS002Support.ibp_scalar u (x := 1) ⟨zero_le_one, le_rfl⟩ ν
  have h2 := NlsGge.ThirdConsultation.KSPS002Support.ibp_scalar u ht ν
  rw [hI, hD, mul_sub, h1, h2]
  ring

theorem core_decomp (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (w : PhysicalL2) {μ : ℂ} (hμ : μ ≠ 0) :
    -Complex.exp (-(2 * Complex.I * μ)) *
      endpointOsc μ (fun t =>
        (∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
          coverRep38 (physicalSobolevEmbed 1 u) s) * coverRep38 w t) =
    -(sobolevPointValue 1 u 1 / (2 * Complex.I * μ)) * endpointOsc μ (coverRep38 w) +
      (Complex.exp (-(Complex.I * μ)) / (2 * Complex.I * μ)) *
        ((∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 w t) +
          NlsGge.ThirdConsultation.KSPS012Support5.Tz (coverRep38 w)
            (coverRep38 (physicalSobolevDerivative38 1 u)) μ) := by
  set uh := coverRep38 (physicalSobolevEmbed 1 u) with huh
  set dh := coverRep38 (physicalSobolevDerivative38 1 u) with hdh
  set c := coverRep38 w with hc
  have hν : (2 * Complex.I * μ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hμ
  have hci : IntervalIntegrable c volume 0 1 := intervalIntegrable_coverRep38_one w
  have hdi : IntervalIntegrable dh volume 0 1 := intervalIntegrable_coverRep38_one _
  have hae := sobolevPointValue_ae 1 u
  have hexpc : Continuous fun t : ℝ => Complex.exp (-(2 * Complex.I * μ * (t : ℂ))) := by fun_prop
  have hJi : IntervalIntegrable (fun t : ℝ => Complex.exp (-(2 * Complex.I * μ * (t : ℂ))) * c t)
      volume 0 1 := hci.continuousOn_mul hexpc.continuousOn
  have hPi : IntervalIntegrable (fun t : ℝ => uh t * c t) volume 0 1 := by
    have := NlsGge.ThirdConsultation.KSPSSupport.h150_prod_integrableOn
      (physicalSobolevEmbed 1 u) w
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr this
  have hTi := NlsGge.ThirdConsultation.KSPS012Support5.Tz_integrable hci hdi μ
  set Dd : ℝ → ℂ := fun t => ∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) * dh s with hDd
  set E1 : ℂ := Complex.exp (2 * Complex.I * μ * ((1 : ℝ) : ℂ)) with hE1
  set pv1 : ℂ := sobolevPointValue 1 u 1 with hpv1
  set Jc : ℂ := ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Complex.I * μ * (t : ℂ))) * c t with hJc
  set P : ℂ := ∫ t in (0 : ℝ)..1, uh t * c t with hP
  set T : ℂ := NlsGge.ThirdConsultation.KSPS012Support5.Tz c dh μ with hT
  have hTdef : T = ∫ t in (0 : ℝ)..1, (Complex.exp (-(2 * Complex.I * μ * (t : ℂ))) * c t) * Dd t := rfl
  -- the main integral identity
  have hmain : (2 * Complex.I * μ) * endpointOsc μ (fun t =>
        (∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) * uh s) * c t) =
      Complex.exp (Complex.I * μ) * (E1 * pv1 * Jc - P - T) := by
    unfold endpointOsc
    rw [← intervalIntegral.integral_const_mul]
    have hpt : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 →
        (2 * Complex.I * μ) * (Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) *
          ((∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) * uh s) * c t)) =
        Complex.exp (Complex.I * μ) * (E1 * pv1 * (Complex.exp (-(2 * Complex.I * μ * (t : ℂ))) * c t) -
          uh t * c t - (Complex.exp (-(2 * Complex.I * μ * (t : ℂ))) * c t) * Dd t) := by
      filter_upwards [hae] with t ht htI
      rw [uIoc_of_le zero_le_one] at htI
      have htI' : t ∈ Icc (0 : ℝ) 1 := ⟨htI.1.le, htI.2⟩
      have hib := ibp_tail u (2 * Complex.I * μ) htI'
      have e1 : Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) =
          Complex.exp (Complex.I * μ) * Complex.exp (-(2 * Complex.I * μ * (t : ℂ))) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      have e2 : Complex.exp (2 * Complex.I * μ * (t : ℂ)) *
          Complex.exp (-(2 * Complex.I * μ * (t : ℂ))) = 1 := by
        rw [← Complex.exp_add]; simp
      have hq : (2 * Complex.I * μ) * ∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) * uh s =
          E1 * pv1 - Complex.exp (2 * Complex.I * μ * (t : ℂ)) * uh t - Dd t := by
        rw [hib, ht]
      calc (2 * Complex.I * μ) * (Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) *
            ((∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) * uh s) * c t))
          = Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) *
            (((2 * Complex.I * μ) * ∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) * uh s) *
              c t) := by ring
        _ = _ := by
          rw [hq, e1]
          linear_combination (-(Complex.exp (Complex.I * μ)) * uh t * c t) * e2
    rw [intervalIntegral.integral_congr_ae hpt]
    have hsplit : ∫ t in (0 : ℝ)..1, Complex.exp (Complex.I * μ) *
        (E1 * pv1 * (Complex.exp (-(2 * Complex.I * μ * (t : ℂ))) * c t) - uh t * c t -
          (Complex.exp (-(2 * Complex.I * μ * (t : ℂ))) * c t) * Dd t) =
        Complex.exp (Complex.I * μ) * (E1 * pv1 * Jc - P - T) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_sub ((hJi.const_mul _).sub hPi) hTi,
        intervalIntegral.integral_sub (hJi.const_mul _) hPi, intervalIntegral.integral_const_mul]
      rfl
    exact hsplit
  have hOc : endpointOsc μ c = Complex.exp (Complex.I * μ) * Jc := by
    unfold endpointOsc
    rw [hJc, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    beta_reduce
    have e1 : Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) =
        Complex.exp (Complex.I * μ) * Complex.exp (-(2 * Complex.I * μ * (t : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e1]; ring
  have hMn : endpointOsc μ (fun t =>
        (∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) * uh s) * c t) =
      (2 * Complex.I * μ)⁻¹ * (Complex.exp (Complex.I * μ) * (E1 * pv1 * Jc - P - T)) := by
    rw [← hmain, ← mul_assoc, inv_mul_cancel₀ hν, one_mul]
  rw [hMn, hOc]
  have eb1 : Complex.exp (-(2 * Complex.I * μ)) * E1 = 1 := by
    rw [hE1, ← Complex.exp_add]; simp
  have eb2 : Complex.exp (-(2 * Complex.I * μ)) * Complex.exp (Complex.I * μ) =
      Complex.exp (-(Complex.I * μ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  generalize Complex.exp (-(2 * Complex.I * μ)) = b at eb1 eb2 ⊢
  generalize Complex.exp (Complex.I * μ) = a at eb2 ⊢
  generalize Complex.exp (-(Complex.I * μ)) = d at eb2 ⊢
  field_simp
  linear_combination (-(a * pv1 * Jc)) * eb1 + (P + T) * eb2

end NlsGge.ThirdConsultation.KSPSWKB
