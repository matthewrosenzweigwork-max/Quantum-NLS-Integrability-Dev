import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.LinearJacobi
import NlsGge.Ramer.AffineJacobi

                                                                                                                     
                                                                                                                     
                                                                                                                     
                                                                                                                  
                                                                                                                  
                                                                                                                  
                                                                                                         
                                                                                                              
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

section R042Production
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "i" => cmEmbedding c s hs
local notation "J" => ramerJac c s hs

/-- R-042 bridge: the RamerSetting06 Jacobian is the production `ramerJac` (ramerJac_eq, as in R041). -/
theorem r042_ramerJac_bridge (M : E → H) (x : E) :
    J M x = NlsGge.Ramer.ramerJac c s hs M x :=
  (NlsGge.Ramer.ramerJac_eq c s hs M x).symm

theorem linear_map_symm
    (A : E →L[ℝ] H) (T : E ≃L[ℝ] E)
    (hT : ∀ x : E, T x = x + i (A x)) :
    (μ).map T.symm = (μ).withDensity
      (fun x : E => ENNReal.ofReal (J (fun y : E => A y) x)) := by
  have h := NlsGge.Ramer.linear_map_symm c s hs A T hT
  have hfun : (fun x : E => ENNReal.ofReal (J (fun y : E => A y) x)) =
      (fun x : E => ENNReal.ofReal (NlsGge.Ramer.ramerJac c s hs (fun y : E => A y) x)) := by
    funext x
    rw [r042_ramerJac_bridge]
  rw [hfun]
  exact h

theorem affine_map_symm
    (A : E →L[ℝ] H) (T : E ≃L[ℝ] E)
    (hT : ∀ x : E, T x = x + i (A x)) (e : H) :
    (μ).map (NlsGge.Ramer.affineHomeo c s hs T e).symm =
      (μ).withDensity (fun x : E => ENNReal.ofReal
        (J (fun y : E => A y + (e + A (i e))) x)) := by
  have h := NlsGge.Ramer.affine_map_symm c s hs A T hT e
  have hfun : (fun x : E => ENNReal.ofReal (J (fun y : E => A y + (e + A (i e))) x)) =
      (fun x : E => ENNReal.ofReal
        (NlsGge.Ramer.ramerJac c s hs (NlsGge.Ramer.affineField c s hs A e) x)) := by
    funext x
    exact congrArg ENNReal.ofReal
      (r042_ramerJac_bridge c s hs (fun y : E => A y + (e + A (i e))) x)
  rw [hfun]
  exact h

end R042Production

end
end NlsGge.ThirdConsultation.R
