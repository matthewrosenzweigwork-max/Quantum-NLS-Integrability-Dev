import Mathlib
import NlsGge.Atomic.G2.G2048
import NlsGge.ThirdConsultation.G2.G2071Support1

/- G2-073 HOST01 (proof development, AUTHOR; not self-reviewed). Host for the design names used by the G2-073 head
   that are not yet landed anywhere in NlsGge/ or in other workers' folders (grep at authoring time:
   normalizedChi, normalizedRemainder, normalizedRootRemainderIntegral: no matches).
   Bodies are verbatim from followup4 DEFINITIONS/G2.lean.md lines 159-170 (namespace NlsGge.GKDefinitionDesign).
   Names bound elsewhere and NOT redeclared here: normalizedRoot (G2071Support1), sourceW/sourceF (SourceFamilyBasic),
   standardRoot (G2019), psiZeta (G2048), discC/discR/tauN (GK38). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def normalizedChi (n m : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  (Real.pi : ℂ)*((n-m : ℤ) : ℂ)*
    psiZeta φ (p2Extend38 n (sourceF n φ)) n m z

def normalizedRemainder (n m : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  dslope (normalizedChi n m φ) (tauN φ m) z

def normalizedRootRemainderIntegral (n m : ℤ) (φ : PotPair) : ℂ :=
  (2*(Real.pi : ℂ)*Complex.I)⁻¹ *
    circleIntegral (fun z => (normalizedRoot n m φ-z)*(z-tauN φ m)/
      standardRoot φ m z * normalizedRemainder n m φ z)
      (discC φ m) (discR φ m)

end
end NlsGge.GKDefinitionDesign
