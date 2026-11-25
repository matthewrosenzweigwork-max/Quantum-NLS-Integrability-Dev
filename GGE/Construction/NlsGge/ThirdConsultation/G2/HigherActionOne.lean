import Mathlib
import NlsGge.ThirdConsultation.G2.G2042Host
import NlsGge.GK38.ActionRealBridge
import NlsGge.GK38.ContourActionDeformation
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38

                                                                                                                       
                                                                                                               
                                                                                                        
                                                                                 
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem higherAction_one_eq_gkActionC38 (φ : PotPair) (n : ℤ) :
    higherAction 1 φ n = gkActionC38 φ n := by
  have hfun : (fun z : ℂ => z^1 * deriv (discrim φ) z / canonRoot38 φ z) =
      actionIntegrand38 φ := by
    funext z
    simp [actionIntegrand38]
  unfold higherAction gkActionC38 contourAction38
  rw [hfun]

theorem higherAction_one_re_eq_action (u : PhysicalL2) (n : ℤ) :
    (higherAction 1 (realSlice u) n).re = actualGapActionAllE02_38 u n := by
  rw [higherAction_one_eq_gkActionC38, NlsGge.GK38.ActionRealBridge.action_real_bridge]
  exact Complex.ofReal_re _

end
end NlsGge.GKDefinitionDesign
