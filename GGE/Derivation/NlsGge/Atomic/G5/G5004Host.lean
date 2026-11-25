import Mathlib
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.DirichletLabels
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

/- G5-004 HOST (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5004Host.lean.
   Bodies byte-identical to Pro round 10 (PRO_DEFINITION_RESPONSE_FP80_10.md, commit 178f84d6) section 7:
   radiusQuotientLeading (the retained G5004 block) and radiusOmittedNormalized (the optional scalar helper block).
   Names checked absent from NlsGge/ (grep) at authoring time. No lexical edits. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def radiusQuotientLeading (n : ℤ) : ℂ := -((-1 : ℂ) ^ n) / 2

def radiusOmittedNormalized (n : ℤ) (φ : PotPair) : ℂ :=
  a5OmittedRootProduct38 n (φ, muSeq φ n) / (Lib.piN n : ℂ)

end
end NlsGge.GKDefinitionDesign
