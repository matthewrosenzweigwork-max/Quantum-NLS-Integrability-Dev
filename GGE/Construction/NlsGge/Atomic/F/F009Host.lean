import Mathlib
import NlsGge.Birkhoff.F05Identity38
import NlsGge.ThirdConsultation.G6.BirkhoffBasic

                                                                                                 
                                                                                                              
                                                                                                                  
                                                                                                     
                                                                                                                 
                                                                                                         
                                                                                                                   
                                                                                                    
set_option autoImplicit false

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F

def lowerSobolev (m : ℕ) (y : SobolevHilbert (m : ℝ)) :
    SobolevHilbert ((m - 1 : ℕ) : ℝ) :=
  ofCarrier38 _
    (NlsGge.Birkhoff.carrierIncl38
      (show ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) from
        Nat.cast_le.mpr (Nat.sub_le m 1)) (toCarrier38 _ y))

def actionQuadratic (m : ℕ) (β : ℕ → ℝ) (u : PhysicalL2) : ℝ :=
  ∑' n : ℤ, finiteHierarchyRate38 m β n *
    ‖NlsGge.GKDefinitionDesign.physicalBirkhoff u n‖ ^ 2

def fourierQuadratic (m : ℕ) (β : ℕ → ℝ)
    (y : SobolevHilbert (m : ℝ)) : ℝ :=
  ∑' n : ℤ, finiteHierarchyRate38 m β n *
    ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2

end NlsGge.ThirdConsultation.F
