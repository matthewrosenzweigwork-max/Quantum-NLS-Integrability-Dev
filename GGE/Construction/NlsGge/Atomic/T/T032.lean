import Mathlib
import NlsGge.ThirdConsultation.T.TDefs2Host
import NlsGge.Birkhoff.W12Tilt38c
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.ThirdConsultation.Common.FiniteSupport

                                                                                                                
                                                                                                               
                                                                                                                      
                                                                                                                      
                                                                                                         
                                                                                                                      
                                                                                                                  
                                                                                                                       
                                                                                              
                                                                                                                    
                                                                                                                      
                                                                                                               
                                                                                                             
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common
open NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.T

theorem lowerWeightTilt_spectralDefect
    (lo up : ℝ) (c : BoundedCoefficients lo up) (delta : ℝ)
    (hd0 : 0 < delta) (hd : delta * up < lo) (u : PhysicalL2)
    (hW : Summable (fun n : ℤ => remainderSummand38 c.val u n))
    (hWt : Summable (fun n : ℤ => remainderSummand38 (tiltCoef38 c.val delta) u n))
    (hA : Summable (fun n : ℤ => bRate38 c.val n * actualGapActionAllE02_38 u n)) :
    EB38 c.val u ≠ ⊤ ∧
    spectralDefect (tiltCoef38 c.val delta) u = spectralDefect c.val u -
      delta * ((EB38 c.val u).toReal -
        ∑' n : ℤ, bRate38 c.val n * actualGapActionAllE02_38 u n) :=
  remainder_tilt_identity38 c hd0 hd u hW hWt hA

end NlsGge.ThirdConsultation.T
