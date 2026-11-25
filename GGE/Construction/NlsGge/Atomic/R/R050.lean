import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.RamerLemma54Eventually

                                                                                                           
                                                                                                                   
                                                                                                               
                                                                                                                    
                                                                                                         
                                                                                                            
                                                                         
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

section R050Production
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "J" => ramerJac c s hs
local notation "Smap" => TM c s hs

theorem ramer_lemma_5_4
    (K G : E → H) (hK : ContDiff ℝ 2 K) (hG : ContDiff ℝ 2 G)
    (U : Set E) (hU : IsOpen U)
    (hNull : NullPreservingOn μ (Smap K) U)
    (hTrunc : EventuallyTruncNullPreserving c s hs K U) :
    ∀ᵐ x ∂μ, x ∈ U →
      J (fun y : E => K y + G (Smap K y)) x =
        J G (Smap K x) * J K x := by
  have h := NlsGge.Ramer.ramer_lemma_5_4_eventually c s hs U hU K G hK hG hNull hTrunc
  have eJ : ∀ (M : E → H) (x : E), ramerJac c s hs M x = NlsGge.Ramer.ramerJac c s hs M x :=
    fun M x => (NlsGge.Ramer.ramerJac_eq c s hs M x).symm
  filter_upwards [h] with x hx hxU
  rw [eJ, eJ G, eJ K]
  exact hx hxU

end R050Production

end
end NlsGge.ThirdConsultation.R
