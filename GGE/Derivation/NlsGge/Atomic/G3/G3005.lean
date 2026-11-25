import Mathlib
import NlsGge.ThirdConsultation.G3.G3005Host
import NlsGge.ThirdConsultation.G3.G3005UpperHost
import NlsGge.ThirdConsultation.G3.G3005Support1
import NlsGge.ThirdConsultation.G3.G3005C2Support
import NlsGge.ThirdConsultation.G3.G3005C4
import NlsGge.ThirdConsultation.G3.G3005C5
import NlsGge.ThirdConsultation.G3.G3005C36
import NlsGge.ThirdConsultation.G3.G3003Host

/- G3_005 PRODUCTION01 (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/G3/G3005.lean, namespace NlsGge.GKDefinitionDesign.
   Head VERBATIM from Pro round 9 (root/gpt6pro_followup7 STATEMENTS/G3.md lines 102-114, file sha256 d03d1697dc4aa6e03b9b1e79040ca8abd3a274af7d74ce40b38fb980def1747a).
   Proof: the six conjuncts are C1 g3005_bank_integrable, C2 g3005_c2_contour, C3 g3005_c3, C4 g3005_c4_nonempty, C5 g3005_c5,
   C6 g3005_c6 (all unconditional; no hypothesis beyond the head). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G3_005 (n m : ℤ) (φ : SourcePotential) (hgap : gap φ.1 m ≠ 0) :
  IntervalIntegrable (betaGapDensity n m φ.1) volume 0 1 ∧
  (∃ s : ℂ, (s = 1 ∨ s = -1) ∧
    betaGapIntegral n m φ.1 = s*(Real.pi : ℂ)*(if m=n then 1 else 0)) ∧
  (m ≠ n → (muSeq φ.1 m = lamMinus φ.1 m ∨
    muSeq φ.1 m = lamPlus φ.1 m) → offDiagonalBeta n m φ.1 = 0) ∧
  Nonempty (UpperStartPath m φ) ∧
  (∀ p : UpperStartPath m φ, ∃ b : ℂ, HasUpperStartIntegral n m φ p b) ∧
  ∀ (p : SourcePath m φ) (q : UpperStartPath m φ) (a b : ℂ),
    HasGKImproperPathIntegral38 n m sourceF (sourceGK φ) p a →
    HasUpperStartIntegral n m φ q b →
    ∃ k : ℤ, a-b =
      (if m=n then (Real.pi : ℂ) else 0) + (k : ℂ)*(2*(Real.pi : ℂ)) :=
  ⟨g3005_bank_integrable n m φ.1 φ.2 hgap, g3005_c2_contour n m φ hgap, g3005_c3 n m φ,
    g3005_c4_nonempty m φ hgap, g3005_c5 n m φ hgap, g3005_c6 n m φ hgap⟩

end
end NlsGge.GKDefinitionDesign
