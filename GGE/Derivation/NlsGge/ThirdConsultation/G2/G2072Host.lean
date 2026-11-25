import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.GK38.AbelianPsiNumerator

/- G2-072 HOST (proof development, AUTHOR; not self-reviewed). Target module NlsGge/ThirdConsultation/G2/G2072Host.lean.
   Hosts the design name `psi`, body verbatim from followup4 DEFINITIONS/G2.lean.md lines 46-47:
   `def psi (n : ℤ) (φ : PotPair) (z : ℂ) : ℂ := p6PsiNumerator38 n (sourceF n) φ z`.
   Shared host: G2-073 and G2-075 import this module and must not redeclare `psi`. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def psi (n : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  p6PsiNumerator38 n (sourceF n) φ z

end
end NlsGge.GKDefinitionDesign
