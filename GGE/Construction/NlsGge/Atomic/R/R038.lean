import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.RamerStep8Bridge

                                                                                                           
                                                                                                                        
                                                                                                                         
                                                                                                                 
                                                 
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section
section R038Main
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "J" => ramerJac c s hs
local notation "Smap" => TM c s hs

/-- **R-038, Fatou lower bound on the localized target** (Pro round 6 head, verbatim). -/
theorem step8c_set
    (L : E → H) (ε : ℝ) (hL : Step8Hyp c s hs L ε)
    (B : Set E) (hB : B ⊆ ball (0 : E) (ε / 2)) :
    (∫⁻ x in localDomain c s ε ∩ (Smap L) ⁻¹' B,
      ENNReal.ofReal (J L x) ∂μ) ≤ μ B :=
  by
  have key : ∀ x : E, ramerJac c s hs L x = NlsGge.Ramer.ramerJac c s hs L x :=
    fun x => (NlsGge.Ramer.ramerJac_eq c s hs L x).symm
  have h := (NlsGge.Ramer.step8c_ramerJac c s hs L hL).2.1 B hB
  simp only [key]
  exact h

end R038Main
end
end NlsGge.ThirdConsultation.R
