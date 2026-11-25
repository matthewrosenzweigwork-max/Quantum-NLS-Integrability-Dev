import Mathlib
import NlsGge.Atomic.G6.G6035Core
import NlsGge.Atomic.G6.G6033
import NlsGge.Atomic.G6.G6034

                                                                                                                 
                                                                                                               
                                                                                                                
                                                                                                         
                                                                    
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6035 :
  (∀ I : PositiveActionSpace,
    coordinateActionsPositive (positiveActionRoot I) = I ∧
    ‖positiveActionRoot I‖^2 = weightedActionNorm I.val) ∧
  (∀ z : SobolevCarrier38 ((1 : ℕ) : ℝ),
    transformedNLSHamiltonian z = actionHamiltonian (coordinateActionsPositive z)) ∧
  (∀ (I : PositiveActionSpace) (z : SobolevCarrier38 ((1 : ℕ) : ℝ)),
    coordinateActionsPositive z = I → transformedNLSHamiltonian z = actionHamiltonian I) :=
  NlsGge.ThirdConsultation.G6035S.G6035_of G6033.2

end
end NlsGge.GKDefinitionDesign
