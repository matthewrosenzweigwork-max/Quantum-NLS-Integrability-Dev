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

/- TDEFS2HOST HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORTING host (no packet increment),
   target NlsGge/ThirdConsultation/T/TDefs2Host.lean. Hosts, VERBATIM and once, every followup13 DEFINITIONS/T.lean.md
   name used by the heads of T-009..T-034 (T-009/010/011/012/014/018/020/023/028/032/033/034) that is not declared in
   NlsGge/, TDefsHost (ZW, fullFourierDensity, muWE; queued q329), T026Host (physicalInclusion, ...), h771's T027Host
   (lowerEnergy) or T028Host (evenCharge): relativePartition (L52), fullFourierLaw (L59), fullFourierWeight (L63),
   spectralDefect (L118) [block L18, preamble L22-28]; muW (L252), ordinarySobolev (L262), fullFourierLawE (L274),
   evenProductOrder (L290), mixedProductOrder (L293), chargeMonomial (L296), signedChargeMonomial (L301)
   [block L241, preamble L242-250]. evenProductOrder/mixedProductOrder are transitive (used by the two monomials).
   Each printed block keeps its own verbatim preamble inside a top-level `section`, so the two open-sets do not mix.
   No reduction applied. Needs ROOT MAIN PROBE. -/
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
