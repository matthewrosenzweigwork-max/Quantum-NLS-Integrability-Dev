import Mathlib
import NlsGge.Atomic.R.R054
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.SpaceTransfer
import NlsGge.Ramer.RamerJacobianHead

                                                                                                          
                                                                                                                    
                                                                                                                    
                                             
                                                                      
                                                                                   
                                                                                    
                                                                                                        
                                                                                            
                                                                                                                      
                                                                                                         
                                                                                                                    
                                                                                                                  
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section
section R055Main
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "J" => ramerJac c s hs
local notation "Smap" => TM c s hs

/-- **R-055, positivity everywhere, integrability, and mass one** (Pro round 6 head, verbatim). -/
theorem ramer_density_positive_integral_one
    (T : E ≃ₜ E) (K Kinv : E → H)
    (hT : RamerHomeomorphismData c s hs T K Kinv) :
    (∀ x : E, 0 < J K x) ∧ Integrable (J K) μ ∧
      (∫ x : E, J K x ∂μ) = 1 := by
  have hmap := ramer_step10_global c s hs T K Kinv hT
  obtain ⟨hK, hK', hT1, hTs1⟩ := hT
  have hK1 : ContDiff ℝ 1 K := hK.of_le (by norm_num)
  have hK'1 : ContDiff ℝ 1 Kinv := hK'.of_le (by norm_num)
  -- The head's Jacobian is the production ramerJE with the coordinate divergence of K.
  have hJeq : J K = NlsGge.Ramer.ramerJE c s hs K (NlsGge.Ramer.ramerDiv c s hs K) := by
    funext x
    exact (NlsGge.Ramer.ramerJE_eq c s hs K (NlsGge.Ramer.ramerDiv c s hs K) x).symm
  -- Positivity at every point (ramerJE_pos uses the inverse-map identities).
  have hpos : ∀ x : E, 0 < J K x := fun x => by
    have h := NlsGge.Ramer.ramerJE_pos c s hs T K Kinv (fun y => hT1 y) (fun y => hTs1 y)
      hK1 hK'1 (NlsGge.Ramer.ramerDiv c s hs K) x
    rw [hJeq]
    exact h
  -- Measurability of the Jacobian (C² field, production divergence spec).
  have hmeas : AEStronglyMeasurable (J K) μ := by
    rw [hJeq]
    exact NlsGge.Ramer.aestronglyMeasurable_ramerJE c s hs K hK1
      (NlsGge.Ramer.ramerDiv c s hs K) (NlsGge.Ramer.ramerDiv_spec c s hs K hK).1
  -- The Gaussian is a probability measure.
  have hprob : IsProbabilityMeasure μ := by
    unfold ramerGaussian
    infer_instance
  -- Mass of the pushforward is one, so the lintegral of the density is one.
  have hone : ∫⁻ x : E, ENNReal.ofReal (J K x) ∂μ = 1 := by
    have h1 : ((μ).map T.symm) Set.univ = 1 := by
      rw [Measure.map_apply T.symm.continuous.measurable MeasurableSet.univ]
      simp
    rw [hmap, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    exact h1
  -- Integrability from the finite lintegral of |J| (J is nonnegative).
  have hint : Integrable (J K) μ := by
    refine ⟨hmeas, ?_⟩
    unfold HasFiniteIntegral
    have hnorm : ∫⁻ x : E, ‖J K x‖ₑ ∂μ = 1 := by
      rw [← hone]
      refine lintegral_congr fun x => ?_
      rw [Real.enorm_of_nonneg (hpos x).le]
    rw [hnorm]
    exact ENNReal.one_lt_top
  refine ⟨hpos, hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => (hpos x).le) hmeas, hone]
  simp

end R055Main
end
end NlsGge.ThirdConsultation.R
