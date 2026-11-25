import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import Armstrong.Work.ActualScalarCartesianModels

/- G3-006 HOST (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/ThirdConsultation/G3/G3006Host.lean, namespace NlsGge.GKDefinitionDesign (as G3003Host, SourceFamilyBasic, G3010Host).
   Hosts the design names `ComplexAngle`, `etaExponential`, `etaRepresentative`, `etaAngle`, bodies VERBATIM from
   DEFINITIONS/G3.lean.md "Quotient-valued eta and theta" (gpt6pro_followup8; byte-identical to followup7). thetaAngle and CongruentPi of the same
   design block are NOT hosted (no G3-006 use; their owners host them).  grep NlsGge/, Armstrong/ and all worker folders (2026-10-31): none of these names
   is defined elsewhere.  gk16ActualScalarZPlus38 is Armstrong.Work.ActualScalarCartesianModels (X-006 closure line 50, no copy needed, like G3003Host's
   gk151BetaAmbient38).  `gap` (G2046) and `sourceF` (SourceFamilyBasic) come in through SourceFamilyBasic. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev ComplexAngle := ℂ ⧸ AddSubgroup.zmultiples (2*(Real.pi : ℂ))

def etaExponential (n : ℤ) (φ : PotPair) : ℂ :=
  gk16ActualScalarZPlus38 sourceF n φ / gap φ n

def etaRepresentative (n : ℤ) (φ : PotPair) : ℂ :=
  -Complex.I * Complex.log (etaExponential n φ)

def etaAngle (n : ℤ) (φ : PotPair) : ComplexAngle :=
  QuotientAddGroup.mk (etaRepresentative n φ)

end
end NlsGge.GKDefinitionDesign
