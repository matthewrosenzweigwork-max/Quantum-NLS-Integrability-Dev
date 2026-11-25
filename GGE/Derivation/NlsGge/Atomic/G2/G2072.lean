import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.GK38.AbelianPsiPeriodNormalization
import NlsGge.ThirdConsultation.G2.G2072Host

/- G2-072 PRODUCTION01 (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/G2/G2072.lean,
   namespace NlsGge.GKDefinitionDesign. Head VERBATIM from followup4 STATEMENTS/G2.md lines 959-961
   (file sha256 844d17175a24ba92649b5d1a4b479aa8a6c53a691840601ab9b9a5a0fbe09c71).
   Proof: the landed GK38 theorem p6PsiNumerator_missing_period38 with F := sourceF n, hφ mapped to gkW by the
   X-006 field W_gk, and hzero from the X-006 field F_zero. No hypothesis is added. psi is the hosted design name. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G2_072 (φ : PotPair) (hφ : φ ∈ sourceW) (n : ℤ) :
    CircleIntegrable (fun z => psi n φ z/canonRoot38 φ z) (discC φ n) (discR φ n) ∧
    abelianPeriod38 n φ (psi n φ) = 2*(Real.pi : ℂ) :=
  p6PsiNumerator_missing_period38 n φ (sourceFamily.W_gk hφ) (sourceF n)
    (sourceFamily.F_zero n φ hφ)

end
end NlsGge.GKDefinitionDesign
