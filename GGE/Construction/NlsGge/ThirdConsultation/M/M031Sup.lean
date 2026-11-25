import Mathlib
import NlsGge.Atomic.G1.G1104Sup
import NlsGge.GK38.PairPotential

   
                                                                                                                    

                                                                                                                    
                                                                                                                         
                                                                                                                
                                                       
  

set_option autoImplicit false

noncomputable section

open MeasureTheory
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

local instance : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

theorem cover_continuous_summable (u : PhysicalL2)
    (hs : Summable (fun k : ℤ => ‖fourierCoeff (naturalPhysicalCoverL2 u) k‖)) :
    Summable (fun k : ℤ => fourierCoeff (naturalPhysicalCoverL2 u) k • fourier (T := (2 : ℝ)) k) := by
  apply Summable.of_norm
  simpa only [norm_smul, fourier_norm, mul_one] using hs

/-- The continuous Fourier sum of the cover (auxiliary). -/
def coverContinuous (u : PhysicalL2)
    (_hs : Summable (fun k : ℤ => ‖fourierCoeff (naturalPhysicalCoverL2 u) k‖)) :
    C(SpectralCircle, ℂ) :=
  ∑' k : ℤ, fourierCoeff (naturalPhysicalCoverL2 u) k • fourier (T := (2 : ℝ)) k

theorem coverContinuous_toLp (u : PhysicalL2)
    (hs : Summable (fun k : ℤ => ‖fourierCoeff (naturalPhysicalCoverL2 u) k‖)) :
    ContinuousMap.toLp 2 spectralHaar ℂ (coverContinuous u hs) = naturalPhysicalCoverL2 u := by
  have h := (ContinuousMap.toLp 2 spectralHaar ℂ).hasSum (cover_continuous_summable u hs).hasSum
  have hl := hasSum_fourier_series_L2 (T := (2 : ℝ)) (naturalPhysicalCoverL2 u)
  simp only [map_smul] at h
  change HasSum (fun k : ℤ => fourierCoeff (naturalPhysicalCoverL2 u) k • fourierLp (T := (2 : ℝ)) 2 k)
    (ContinuousMap.toLp 2 spectralHaar ℂ (coverContinuous u hs)) at h
  exact h.unique hl

theorem coverContinuous_norm_le (u : PhysicalL2)
    (hs : Summable (fun k : ℤ => ‖fourierCoeff (naturalPhysicalCoverL2 u) k‖)) (x : SpectralCircle) :
    ‖coverContinuous u hs x‖ ≤ ∑' k : ℤ, ‖fourierCoeff (naturalPhysicalCoverL2 u) k‖ := by
  refine (ContinuousMap.norm_coe_le_norm _ x).trans ?_
  calc ‖coverContinuous u hs‖
      ≤ ∑' k : ℤ, ‖fourierCoeff (naturalPhysicalCoverL2 u) k • fourier (T := (2 : ℝ)) k‖ :=
        norm_tsum_le_tsum_norm (by simpa only [norm_smul, fourier_norm, mul_one] using hs)
    _ = ∑' k : ℤ, ‖fourierCoeff (naturalPhysicalCoverL2 u) k‖ := by
        simp only [norm_smul, fourier_norm, mul_one]

/-- Pro round 14 M-031 support E3. -/
theorem sourceIntervalClass_ae_le (u : PhysicalL2)
    (hs : Summable (fun k : ℤ => ‖fourierCoeff (naturalPhysicalCoverL2 u) k‖)) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖NlsGge.GKDefinitionDesign.sourceIntervalClass u t‖ ≤
        ∑' k : ℤ, ‖fourierCoeff (naturalPhysicalCoverL2 u) k‖ := by
  have hrep : (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) =ᵐ[spectralHaar] coverContinuous u hs := by
    have := ContinuousMap.coeFn_toLp (p := 2) (μ := spectralHaar) (𝕜 := ℂ) (coverContinuous u hs)
    rw [coverContinuous_toLp u hs] at this
    exact this
  have hcirc : ∀ᵐ x ∂spectralHaar, ‖naturalPhysicalCoverL2 u x‖ ≤
      ∑' k : ℤ, ‖fourierCoeff (naturalPhysicalCoverL2 u) k‖ := by
    filter_upwards [hrep] with x hx
    rw [hx]
    exact coverContinuous_norm_le u hs x
  have hreal : ∀ᵐ t : ℝ, ‖coverRep38 u t‖ ≤ ∑' k : ℤ, ‖fourierCoeff (naturalPhysicalCoverL2 u) k‖ :=
    ae_real_of_ae_spectral hcirc
  filter_upwards [ae_restrict_of_ae hreal, (NlsGge.Atomic.G1104Sup.sourceIntervalClass_spec u).2]
    with t ht hcl
  rw [hcl]
  exact ht

end NlsGge.ThirdConsultation.M

end
