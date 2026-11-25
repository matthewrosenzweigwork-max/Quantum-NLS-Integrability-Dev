import Mathlib
import NlsGge.Atomic.G4.G4NormalizedHost
import NlsGge.GK38.AbelianPsiNumerator
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.GradFundamentalDefs
import NlsGge.GK38.DirichletRealReality
import NlsGge.GK38.DirichletLabels
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

/- G5001 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5001Host.lean.
   Bodies byte-identical to Pro round 9 (gpt6pro_followup7 PRO_DEFINITION_RESPONSE_FP80_09.md):
   terminalRoot from section 11 (lines ~1087-1091, the native body; the Armstrong gk16TerminalRoot38 alias is
   not used), then InteriorRealDirichletGap, radiusQuotient, signedRadius from section 12 (lines ~1239-1255).
   No lexical edits were needed (no lambda binder). Names checked absent from NlsGge (only KSN002 has an
   unrelated terminalRoot abbrev in NlsGge.ThirdConsultation.KSN). NOTE for root: proof development's draft
   G4036Host_HOST01.lean.txt also defines NlsGge.GKDefinitionDesign.terminalRoot verbatim; only one may land. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

-- Actual terminal sheet, including complex collapsed gaps.
def terminalRoot (n : ℤ) (φ : PotPair) : ℂ :=
  antiDiscrim φ (muSeq φ n) /
    (((2 * Complex.I) / (Lib.piN n : ℂ)) *
      a5OmittedRootProduct38 n (φ, muSeq φ n))

def InteriorRealDirichletGap (n : ℤ) (u : PhysicalL2) : Prop :=
  NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n < gkMu u n ∧
  gkMu u n < NlsGge.SpectralFoundations.actualGapUpperAllE02_38 u n

def radiusQuotient (n : ℤ) (φ : PotPair) : ℂ :=
  normalizedZeta n φ (muSeq φ n) /
    p6PsiNumerator38 n (sourceF n) φ (muSeq φ n)

def signedRadius (n : ℤ) (φ : PotPair) : ℂ :=
  -Complex.I * terminalRoot n φ

end
end NlsGge.GKDefinitionDesign
