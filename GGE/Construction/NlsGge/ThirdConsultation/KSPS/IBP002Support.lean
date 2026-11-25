import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.Spectral.ActualH1ACRepresentativeUniformBox38V1
import NlsGge.Spectral.ComplexACPointwiseTestIntegrationByPartsV2

                                                                                                                
                                                                                                             
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

namespace NlsGge.ThirdConsultation.KSPS002Support

theorem embed_h1_summable (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    SobolevSquareSummable 1 (physicalFourier (physicalSobolevEmbed 1 u)) := by
  have h1 := (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) (physicalSobolevEmbed 1 u)).mp (by
    have hm := carrierCoe38_mem ((1 : ℕ) : ℝ) (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u)
    have he : fourierSeq38 (physicalSobolevEmbed 1 u) =
        carrierCoe38 ((1 : ℕ) : ℝ) (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u) :=
      funext (physicalSobolevEmbed_fourier 1 u)
    rw [he]; exact hm)
  simpa using h1

theorem continuous_eq_h1 (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    physicalSobolevContinuous38 1 le_rfl u =
      physicalH1Continuous (physicalSobolevEmbed 1 u) (embed_h1_summable u) := by
  have : spatialMeasure.IsOpenPosMeasure := by
    unfold spatialMeasure
    infer_instance
  apply ContinuousMap.toLp_injective (p := 2) (μ := spatialMeasure) (𝕜 := ℂ)
  rw [physicalSobolevContinuous38_toLp, physicalH1Continuous_toLp]

theorem uAderiv_eq (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    uA_deriv (physicalSobolevEmbed 1 u) (embed_h1_summable u) =
      physicalSobolevDerivative38 1 u := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply, uA_deriv_fourier,
    physicalSobolevDerivative38_fourier, pow_one]
  rfl


theorem ibp_scalar (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (ν : ℂ) :
    ν * ∫ t in (0 : ℝ)..x, Complex.exp (ν * (t : ℂ)) * coverRep38 (physicalSobolevEmbed 1 u) t =
      Complex.exp (ν * (x : ℂ)) * sobolevPointValue 1 u x - sobolevPointValue 1 u 0 -
        ∫ t in (0 : ℝ)..x, Complex.exp (ν * (t : ℂ)) *
          coverRep38 (physicalSobolevDerivative38 1 u) t := by
  set E1 := physicalSobolevEmbed 1 u with hE1
  set D := physicalSobolevDerivative38 1 u with hD
  have hu := embed_h1_summable u
  set f : ℝ → ℂ := fun t => physicalH1Continuous E1 hu (t : PhysicalCircle) with hf
  set g : ℝ → ℂ := coverRep38 D with hg
  have hpv : ∀ y : ℝ, sobolevPointValue 1 u y = f y := by
    intro y
    simp only [sobolevPointValue, le_refl, dite_true, hf]
    rw [continuous_eq_h1]
  have hI1 : IntervalIntegrable g volume 0 1 := intervalIntegrable_coverRep38_one D
  have hIx : IntervalIntegrable g volume 0 x := hI1.mono_set (by
    rw [Set.uIcc_of_le hx.1, Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl hx.2)
  have hS : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      (actualPhysicalL2SourcePotential D : ℝ → ℂ) s = g s := by
    filter_upwards [actualPhysicalL2SourcePotential_ae D,
      MeasureTheory.ae_restrict_of_ae (coverRep38_ae_phys D)] with s h1 h2
    rw [h1, hg, h2]
  have hprim : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = f 0 + ∫ s in (0 : ℝ)..t, g s := by
    intro t ht
    have h := uA_integral_deriv E1 hu t ht
    rw [uAderiv_eq] at h
    have h' : ∫ s in (0 : ℝ)..t, (actualPhysicalL2SourcePotential D : ℝ → ℂ) s =
        ∫ s in (0 : ℝ)..t, g s := by
      refine intervalIntegral.integral_congr_ae ?_
      have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ioc (0 : ℝ) 1 := Set.Ioc_subset_Ioc le_rfl ht.2
      have := (ae_restrict_iff' measurableSet_Ioc).mp hS
      filter_upwards [this] with s hs hmem
      rw [Set.uIoc_of_le ht.1] at hmem
      exact hs (hsub hmem)
    rw [h'] at h
    simp only [hf]
    rw [h]; ring
  have hprimx : ∀ t ∈ Set.uIcc (0 : ℝ) x, f t = f 0 + ∫ s in (0 : ℝ)..t, g s := by
    intro t ht
    rw [Set.uIcc_of_le hx.1] at ht
    exact hprim t ⟨ht.1, ht.2.trans hx.2⟩
  have hAC : AbsolutelyContinuousOnInterval f 0 x := by
    have hp := NlsGge.SpectralFoundations.complex_intervalIntegral_primitive_absolutelyContinuousV2
      hIx (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) x)
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => f 0) 0 x :=
      (contDiffOn_const (c := f 0) (n := 1) (s := Set.uIcc (0 : ℝ) x)).absolutelyContinuousOnInterval
    have hs := hc.add hp
    exact hs.congr (fun t ht => (hprimx t ht).symm)
  have hder : ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) x → HasDerivAt f (g t) t := by
    have h0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by simp [ae_iff, measure_singleton]
    have h1 : ∀ᵐ y : ℝ ∂volume, y ≠ x := by simp [ae_iff, measure_singleton]
    filter_upwards [hIx.ae_hasDerivAt_integral, h0, h1] with y hy hy0 hy1 hmem
    have hd := (hy hmem 0 (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) x)).const_add (f 0)
    refine hd.congr_of_eventuallyEq ?_
    rw [Set.uIcc_of_le hx.1] at hmem
    have hmem' : y ∈ Set.Ioo (0 : ℝ) x :=
      ⟨lt_of_le_of_ne hmem.1 (Ne.symm hy0), lt_of_le_of_ne hmem.2 hy1⟩
    filter_upwards [Ioo_mem_nhds hmem'.1 hmem'.2] with z hz
    exact hprimx z (by rw [Set.uIcc_of_le hx.1]; exact ⟨hz.1.le, hz.2.le⟩)
  have hψ : ∀ t ∈ Set.uIcc (0 : ℝ) x, HasDerivAt (fun s : ℝ => Complex.exp (ν * (s : ℂ)))
      (ν * Complex.exp (ν * (t : ℂ))) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => ν * (s : ℂ)) ν t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul ν
    have h2 := h1.cexp
    convert h2 using 1
    ring
  have hψint : IntervalIntegrable (fun t : ℝ => ν * Complex.exp (ν * (t : ℂ))) volume 0 x :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hibp := NlsGge.SpectralFoundations.complex_ac_pointwise_test_integration_by_parts
    hAC hIx hder hψ hψint
  -- convert the representative integrals
  have hrep : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) x →
      Complex.exp (ν * (t : ℂ)) * coverRep38 E1 t = Complex.exp (ν * (t : ℂ)) * f t := by
    have hc := uA_continuous_rep_ae E1 hu
    have hsub : Set.Ioc (0 : ℝ) x ⊆ Set.Ioc (0 : ℝ) 1 := Set.Ioc_subset_Ioc le_rfl hx.2
    have := (ae_restrict_iff' measurableSet_Ioc).mp hc
    filter_upwards [this] with t ht hmem
    rw [Set.uIoc_of_le hx.1] at hmem
    have h3 : f t = coverRep38 E1 t := ht (hsub hmem)
    rw [h3]
  rw [intervalIntegral.integral_congr_ae hrep, hpv, hpv]
  have e1 : (∫ t in (0 : ℝ)..x, f t * (ν * Complex.exp (ν * (t : ℂ)))) =
      ν * ∫ t in (0 : ℝ)..x, Complex.exp (ν * (t : ℂ)) * f t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  have e2 : (∫ t in (0 : ℝ)..x, g t * Complex.exp (ν * (t : ℂ))) =
      ∫ t in (0 : ℝ)..x, Complex.exp (ν * (t : ℂ)) * g t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  rw [e1, e2] at hibp
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hibp
  rw [hibp]
  ring



theorem term1_01 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    volterraTerm 1 x lam φ 0 1 =
      Complex.I * Complex.exp (-(Complex.I * lam * (x : ℂ))) *
        ∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * lam) * (t : ℂ)) *
          coverRep38 (physicalSobolevEmbed 1 φ.1) t := by
  unfold volterraTerm
  simp only [KSPSVolterra.term, KSPSVolterra.integrateMatrix]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp [KSPSVolterra.E, KSPSVolterra.R, KSPSVolterra.phi, Matrix.mul_apply, Fin.sum_univ_two,
    KSPSVolterra.toPair, potRepFst38]
  change Complex.exp (-(Complex.I * lam * ((x : ℂ) - (t : ℂ)))) * Complex.I *
      coverRep38 (physicalSobolevEmbed 1 φ.1) t * Complex.exp (Complex.I * lam * (t : ℂ)) = _
  have he : Complex.exp (-(Complex.I * lam * ((x : ℂ) - (t : ℂ)))) *
      Complex.exp (Complex.I * lam * (t : ℂ)) =
      Complex.exp (-(Complex.I * lam * (x : ℂ))) *
        Complex.exp (2 * Complex.I * lam * (t : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  linear_combination (Complex.I * coverRep38 (physicalSobolevEmbed 1 φ.1) t) * he

theorem term1_10 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    volterraTerm 1 x lam φ 1 0 =
      -Complex.I * Complex.exp (Complex.I * lam * (x : ℂ)) *
        ∫ t in (0 : ℝ)..x, Complex.exp ((-(2 * Complex.I * lam)) * (t : ℂ)) *
          coverRep38 (physicalSobolevEmbed 1 φ.2) t := by
  unfold volterraTerm
  simp only [KSPSVolterra.term, KSPSVolterra.integrateMatrix]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp [KSPSVolterra.E, KSPSVolterra.R, KSPSVolterra.phi, Matrix.mul_apply, Fin.sum_univ_two,
    potRepSnd38]
  change Complex.exp (Complex.I * lam * ((x : ℂ) - (t : ℂ))) * Complex.I *
      coverRep38 (physicalSobolevEmbed 1 φ.2) t * Complex.exp (-(Complex.I * lam * (t : ℂ))) = _
  have he : Complex.exp (Complex.I * lam * ((x : ℂ) - (t : ℂ))) *
      Complex.exp (-(Complex.I * lam * (t : ℂ))) =
      Complex.exp (Complex.I * lam * (x : ℂ)) *
        Complex.exp (-(2 * Complex.I * lam * (t : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  linear_combination (Complex.I * coverRep38 (physicalSobolevEmbed 1 φ.2) t) * he

theorem term1_00 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) : volterraTerm 1 x lam φ 0 0 = 0 := by
  unfold volterraTerm
  simp [KSPSVolterra.term, KSPSVolterra.integrateMatrix, KSPSVolterra.E, KSPSVolterra.R,
    KSPSVolterra.phi, Matrix.mul_apply, Fin.sum_univ_two]

theorem term1_11 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) : volterraTerm 1 x lam φ 1 1 = 0 := by
  unfold volterraTerm
  simp [KSPSVolterra.term, KSPSVolterra.integrateMatrix, KSPSVolterra.E, KSPSVolterra.R,
    KSPSVolterra.phi, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_01 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    oscillatoryPotentialDerivative φ x lam 0 1 =
      ∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * lam) * (t : ℂ)) *
          coverRep38 (physicalSobolevDerivative38 1 φ.1) t := by
  unfold oscillatoryPotentialDerivative
  simp only [KSPSVolterra.P, KSPSVolterra.integrateMatrix]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp [KSPSVolterra.E, KSPSVolterra.phiPrime, Matrix.mul_apply, Fin.sum_univ_two]
  left
  congr 1
  ring

theorem P_10 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    oscillatoryPotentialDerivative φ x lam 1 0 =
      ∫ t in (0 : ℝ)..x, Complex.exp ((-(2 * Complex.I * lam)) * (t : ℂ)) *
          coverRep38 (physicalSobolevDerivative38 1 φ.2) t := by
  unfold oscillatoryPotentialDerivative
  simp only [KSPSVolterra.P, KSPSVolterra.integrateMatrix]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp [KSPSVolterra.E, KSPSVolterra.phiPrime, Matrix.mul_apply, Fin.sum_univ_two]
  left
  congr 1
  ring

theorem P_00 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    oscillatoryPotentialDerivative φ x lam 0 0 = 0 := by
  unfold oscillatoryPotentialDerivative
  simp [KSPSVolterra.P, KSPSVolterra.integrateMatrix, KSPSVolterra.E, KSPSVolterra.phiPrime,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem P_11 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    oscillatoryPotentialDerivative φ x lam 1 1 = 0 := by
  unfold oscillatoryPotentialDerivative
  simp [KSPSVolterra.P, KSPSVolterra.integrateMatrix, KSPSVolterra.E, KSPSVolterra.phiPrime,
    Matrix.mul_apply, Fin.sum_univ_two]

end NlsGge.ThirdConsultation.KSPS002Support
