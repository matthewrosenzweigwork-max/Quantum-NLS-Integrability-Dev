import Mathlib
import NlsGge.Atomic.AL.AL080
import NlsGge.Hierarchy.ALFreeDeterminant38

                                                                               
                                                                                                                
                                                                                                                 
                                                                 
set_option autoImplicit false

open NlsGge.Pilot NlsGge.AblowitzLadik NlsGge.Weights Filter Topology

namespace NlsGge.ThirdConsultation.AL

theorem al092 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    Tendsto (fun N : ℕ =>
      alMeshStep38 N ^ (3 / 2 : ℝ) * alFreeLogDet38 c.val N) atTop
      (𝓝 (8 * ∫ x in (0 : ℝ)..1 / 2, alFreeDetIntegrand38 x)) ∧
    (8 * ∫ x in (0 : ℝ)..1 / 2, alFreeDetIntegrand38 x) < 0 :=
  ⟨alFreeDeterminant_tendsto38 (al080Aux.admissible c), by
    linarith [alFreeDetIntegral_neg38]⟩

end NlsGge.ThirdConsultation.AL
