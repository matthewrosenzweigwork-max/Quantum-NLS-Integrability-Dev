import Mathlib
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.ThirdConsultation.G3.G3003Host

/- G5-018/G5-020 HOST (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5018Host.lean.
   Bodies verbatim from Pro round 13 section 5 (PRO_DEFINITION_RESPONSE_FP80_13.md, "Accept exactly the candidate alias"),
   scope as stated there.  Binding confirmed by Pro: beta m n = offDiagonalBeta n m (m = moving endpoint index, n = angle index);
   beta n n = 0; diagonal endpoint integral is angleIntegralDerivative n n.  Grep of NlsGge/ (2026-11-01): neither name landed. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
noncomputable section

def beta (m n : ℤ) : PotPair → ℂ := offDiagonalBeta n m

def angleIntegralDerivative (m n : ℤ) (φ : PotPair) : PotPair →L[ℂ] ℂ :=
  if m = n then angleDerivative n φ - fderiv ℂ (betaSum n) φ
  else fderiv ℂ (beta m n) φ

end
end NlsGge.GKDefinitionDesign
