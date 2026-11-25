import Mathlib
import NlsGge.Hierarchy.A01Spectral38
import NlsGge.Hierarchy.ExponentialH2Moment38
import NlsGge.Hierarchy.RelativePartition38
import NlsGge.Birkhoff.F09Limit38
import NlsGge.Birkhoff.W07Probability38
import NlsGge.Birkhoff.S03Measure38b
import NlsGge.Birkhoff.W09Approx38
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Birkhoff.F11Claim38d
import NlsGge.Birkhoff.S04Moments38d
import NlsGge.Birkhoff.SignedMoments38f
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev38.SobolevCarrier38
import NlsGge.Measure.CountableReconstruction
import NlsGge.Weights.Entire
import NlsGge.ThirdConsultation.I.LimitLaws
import NlsGge.ThirdConsultation.T.ECarrier98
import NlsGge.ThirdConsultation.Common.FiniteSupport

                                                                                                                   
                                                                                                                      
                                                                                                                     
                                                                                                                     
                                                                                                                  
                                                                                                                  
                                                                                                        
                                                                                                                  
                                                                                                                    
                                                  
set_option autoImplicit false

section TBlockA
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.T
noncomputable section

def relativePartition {lo up : ℝ}
    (c : BoundedCoefficients lo up) (N : ℕ) : ℝ :=
  relativePartition38 c N

def fullFourierLaw {lo up : ℝ}
    (c : BoundedCoefficients lo up) (N : ℕ) : Measure PhysicalL2 :=
  nuWN38 c N

def fullFourierWeight {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (N : ℕ) : ECarrier38 c s → ℝ :=
  fN38 c s N

def spectralDefect (c : ℕ → ℝ) (u : PhysicalL2) : ℝ :=
  NlsGge.Birkhoff.remainder38 c u

end
end NlsGge.ThirdConsultation.T
end TBlockA

section TBlockB
open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Birkhoff
open NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.T
noncomputable section

def muW {lo up : ℝ} (c : BoundedCoefficients lo up) : Measure PhysicalL2 :=
  I.physicalLaw (weight c.val)

def ordinarySobolev {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s r : ℝ) : ECarrier38 c s → SobolevHilbert r :=
  fun x => ofCarrier38 r (reflCF11_38 r (eToSob38 c s r x))

def fullFourierLawE {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (N : ℕ) : Measure (ECarrier38 c s) :=
  ENNReal.ofReal (relativePartition c N)⁻¹ •
    (((fullWeightedSequenceGaussian c s).withDensity
      (fun x => ENNReal.ofReal (fN38 c s N x))).map (projE38 c s N))

def evenProductOrder (indices : Finset ℕ) : ℕ :=
  max 1 (indices.sup id)

def mixedProductOrder (signedIndices evenIndices : Finset ℕ) : ℕ :=
  max 1 (max (evenIndices.sup id) (signedIndices.sup (fun j => j + 1)))

def chargeMonomial (indices : Finset ℕ) (powers : ℕ → ℕ)
    (u : PhysicalL2) : ℝ :=
  ∏ j ∈ indices, (chargeFn38 (evenProductOrder indices + 1) j u) ^ powers j

def signedChargeMonomial (signedIndices evenIndices : Finset ℕ)
    (powersSigned powersEven : ℕ → ℕ) (u : PhysicalL2) : ℝ :=
  let r := mixedProductOrder signedIndices evenIndices
  (∏ j ∈ signedIndices, (oddChargeFn38 (r + 1) j u) ^ powersSigned j) *
    ∏ j ∈ evenIndices, (chargeFn38 (r + 1) j u) ^ powersEven j

end
end NlsGge.ThirdConsultation.T
end TBlockB
