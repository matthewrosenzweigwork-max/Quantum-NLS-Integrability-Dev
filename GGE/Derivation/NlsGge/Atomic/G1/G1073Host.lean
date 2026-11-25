import NlsGge.GK38.PairRealBridge

/- G1-073 HOST01 (proof development, AUTHOR; not reviewed). Hosts the Pro design predicate `simplePeriodic`
   (STATEMENTS/G1.md G1-073 via root/gpt6pro_followup7 DEFINITIONS/G1.lean.md, body verbatim).
   Grep check: no `def simplePeriodic` in NlsGge/ (production) or any other Work folder except Pro root responses. -/
set_option autoImplicit false

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def simplePeriodic (φ : PotPair) (z : ℂ) : Prop :=
  perChar φ z = 0 ∧ deriv (perChar φ) z ≠ 0

end
end NlsGge.GKDefinitionDesign
