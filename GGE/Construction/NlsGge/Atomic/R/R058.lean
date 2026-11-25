import Mathlib
import NlsGge.Atomic.R.R029
import NlsGge.Atomic.R.R054
import NlsGge.Atomic.R.R055
import NlsGge.ThirdConsultation.R.R058Support
import NlsGge.ThirdConsultation.R.RamerSetting06B

                                                                                                          
                                                                                                                                
                                                                                                                             
                                                                                                                                    
                                                                                                                        
                                                                                               
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section
section R058Main
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "i" => cmEmbedding c s hs

/-- **R-058, full `E_s` Ramer theorem** (Pro round 6 head, verbatim). -/
theorem ramer_eq_Ramercommon_C2
    (T : E ≃ₜ E) (K Kinv : E → H)
    (hK : ContDiff ℝ 2 K) (hKi : ContDiff ℝ 2 Kinv)
    (hT : ∀ x : E, T x = x + i (K x))
    (hTi : ∀ y : E, T.symm y = y + i (Kinv y)) :
    ∃ d : E → ℝ, RamerDensityConclusion c s hs T K d := by
  have hdata : RamerHomeomorphismData c s hs T K Kinv := ⟨hK, hKi, hT, hTi⟩
  obtain ⟨d, hV, hLim, -⟩ := exists_v2_local_closedDivergence c s hs K hK
  have hdD := v2_div_ae_eq_ramerDiv c s hs K hK d hLim
  have hJ : jacobianWithDiv c s hs K d =ᵐ[μ] ramerJac c s hs K := by
    filter_upwards [hdD] with x hx
    simp only [jacobianWithDiv, ramerJac, hsDerivH, hx]
  obtain ⟨hpos, hint, hone⟩ := ramer_density_positive_integral_one c s hs T K Kinv hdata
  refine ⟨d, hV, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ramer_step10_global c s hs T K Kinv hdata]
    refine withDensity_congr_ae ?_
    filter_upwards [hJ] with x hx
    rw [hx]
  · intro x
    have h := hpos x
    unfold ramerJac at h
    have hdet : 0 < |NlsGge.Analysis.RegularizedDeterminant.det2 (hsDerivH c s hs K x)| :=
      (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 h
    unfold jacobianWithDiv
    exact mul_pos hdet (Real.exp_pos _)
  · exact hint.congr hJ.symm
  · exact (integral_congr_ae hJ).trans hone
  · exact (tendstoInMeasure_cylindricalDensity_ramerJac c s hs K hK).congr
      (fun _ => Filter.EventuallyEq.refl _ _) hJ.symm

end R058Main
end
end NlsGge.ThirdConsultation.R
