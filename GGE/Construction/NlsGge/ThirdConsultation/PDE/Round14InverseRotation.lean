import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14Rotation
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff
import NlsGge.ThirdConsultation.Common.FiniteSupport

                                                                                   
                                                                                                    
                                                                                                             
                                                                                                                        
                                                                                                                     
                                                                                                             
                                                                                              
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.NLS38 NlsGge.GKDefinitionDesign NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def inverseRotationCurve (z0 : NlsGge.GK38.Lib.L2Z)
    (hz : FiniteSupportSequence z0) (t : ℝ) :
    PhysicalSobolev38 ((3 : ℕ) : ℝ) :=
  inverseBirkhoffSobolev 3 (rotationCurve ((3 : ℕ) : ℝ) z0 hz t)

def inverseRotationPhysical (z0 : NlsGge.GK38.Lib.L2Z)
    (hz : FiniteSupportSequence z0) (t : ℝ) : PhysicalL2 :=
  physicalSobolevEmbed 3 (inverseRotationCurve z0 hz t)

end
end NlsGge.ThirdConsultation.PDE
