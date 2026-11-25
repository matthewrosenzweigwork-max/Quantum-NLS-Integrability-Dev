import Mathlib
import NlsGge.ThirdConsultation.I.LimitLaws
import NlsGge.Weights.Entire
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.ThirdConsultation.R.R109Host
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.ThirdConsultation.T.ECarrier98
import NlsGge.Hierarchy.ExponentialH2Moment38
import NlsGge.Measure.CountableReconstruction

                                                                                                                  
                                                                                                                     
                                                                                                             
                                                                                                                      
                                                                                                             
                                                                                                                  
                                                                                                            
                                                                                                            
set_option autoImplicit false
open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Birkhoff
open NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.T
noncomputable section

def ZW {lo up : ℝ} (c : BoundedCoefficients lo up) : ℝ :=
  I.limitNormalizer (weight c.val)

def fullFourierDensity {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ECarrier38 c s → ℝ :=
  fW06_38 c s hs
    (PDE.actualBirkhoffInput38.KW06_38 PDE.actualOneSmoothingInput38 c
      (le_one_of_lt_three_quarters_W06_38 hs'))
    (R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs'))

def muWE {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    Measure (ECarrier38 c s) :=
  ENNReal.ofReal (ZW c)⁻¹ •
    (fullWeightedSequenceGaussian c s).withDensity
      (fun x => ENNReal.ofReal (fullFourierDensity c s hs hs' x))

end
end NlsGge.ThirdConsultation.T
