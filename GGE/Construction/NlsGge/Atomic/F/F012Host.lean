import Mathlib
import NlsGge.Birkhoff.F05Identity38
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff
import NlsGge.Atomic.F.F027

                                                                                                 
                                                                                                                 
                                                                                                                        
                                                                                          
                                                                                              
                                                                                                         
                                                                                                       
                                                                                                                  
                                                                                                   
                                                                                                                 
                                                                                                                     
                                                                                             
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F
open NlsGge.GKDefinitionDesign

def finiteT (m : ℕ) (x : Hm1 m) : Hm1 m :=
  ofCarrier38 _ (birkhoffSobolev (m - 1)
    ((physicalSobolevFourierEquiv38 ((m - 1 : ℕ) : ℝ)).symm
      (toCarrier38 _ x)))

def finiteA (m : ℕ) (β : ℕ → ℝ) (x : Hm1 m) : ℝ :=
  ∑' n : ℤ, finiteHierarchyRate38 m β n * ‖sobolevCoe _ x n‖ ^ 2

def finiteD (m : ℕ) (β : ℕ → ℝ) (x : Hm1 m) : ℝ :=
  Vm38 m β (FinvH38 m x) - Rm38 m β (FinvH38 m x)

end NlsGge.ThirdConsultation.F
