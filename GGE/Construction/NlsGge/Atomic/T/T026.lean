import Mathlib
import NlsGge.ThirdConsultation.T.T026Host
import NlsGge.ThirdConsultation.T.T026Core
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing

                                                                                                 
                                                                                                                
                                                                                                     
                                                                                                  
                                                                                                                     
                                                                                                       
                                                                           
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.T

theorem lowerEnergy_uniform_tail
    (lo up : ℝ) (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4)
    (u : ℕ → ECarrier38 c s) (hu : convergentWeightedFields c s u) :
    UniformVanishingTails
      (fun N n => lowerEnergyGapTerms c (physicalInclusion c s (u N)) n) :=
  NlsGge.ThirdConsultation.T026X.bGap_uniform_tail
    NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
    NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38 c s hs' u hu

end NlsGge.ThirdConsultation.T
