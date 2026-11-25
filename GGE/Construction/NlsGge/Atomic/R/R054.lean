import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.RamerStep10

                                                                                                           
                                                                                                                                    
                                                                                                                           
                                                                                                                               
                                                                                                                       
                                                                                                                            
                                                                                                                                  
                                                                     
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section
section R054Main
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "J" => ramerJac c s hs
local notation "Smap" => TM c s hs

/-- **R-054, global inverse-pushforward by patching** (Pro round 6 head, verbatim). -/
theorem ramer_step10_global
    (T : E ≃ₜ E) (K Kinv : E → H)
    (hT : RamerHomeomorphismData c s hs T K Kinv) :
    (μ).map T.symm = (μ).withDensity
      (fun x : E => ENNReal.ofReal (J K x)) := by
  obtain ⟨hK, hK', hT1, hTs1⟩ := hT
  unfold ramerGaussian
  obtain ⟨Jt, -, hJae, hmap⟩ :=
    NlsGge.Ramer.ramer_step10_global c s hs T K Kinv hK hK' (fun x => hT1 x) (fun y => hTs1 y)
  have hJae' : Jt =ᵐ[NlsGge.Measure.fullWeightedSequenceGaussian c s]
      fun x : E => ENNReal.ofReal (J K x) := by
    filter_upwards [hJae] with x hx
    rw [hx]
    exact congrArg ENNReal.ofReal (NlsGge.Ramer.ramerJac_eq c s hs K x)
  rw [hmap]
  exact withDensity_congr_ae hJae'

end R054Main
end
end NlsGge.ThirdConsultation.R
