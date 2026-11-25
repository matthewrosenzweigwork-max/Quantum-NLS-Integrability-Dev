import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS015Host
import NlsGge.ThirdConsultation.KSPS.KSPS020Host
import NlsGge.ThirdConsultation.KSPS.KSPS023Host

/- KSPS-027 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS027Host.lean.
   Body VERBATIM from the round-14 active page followup12 DEFINITIONS/KSPS.lean.md, "Retained design-only bodies"
   (`NlsGge.ThirdConsultation.KSPS.UnorderedEndpointExpansion`; Pro round 14 Cluster 1: retained bodies are hosted once;
   KSPS-027 "unchanged"). grep of NlsGge/ and Work/isolated_20261027 (2026-11-01): no UnorderedEndpointExpansion.
   Uses WeightedL2Error (KSPS015Host), periodicMinus/Plus (KSPS020Host), spectralPolynomial (KSPS023Host).
   Header opens = Pro's block for those bodies (as KSPS023Host). `Complex.sqrt` is Mathlib's (RCLike/Sqrt). No repair. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common NlsGge.ThirdConsultation
open NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def UnorderedEndpointExpansion (N : ℕ) (φ : SobolevC N) (s : ℝ) : Prop :=
  ∃ eplus eminus : ℤ → ℂ,
    WeightedL2Error s eplus ∧ WeightedL2Error s eminus ∧
    ∀ᶠ n : ℤ in Filter.cocompact ℤ,
      ({periodicMinus φ n, periodicPlus φ n} : Multiset ℂ) =
        {spectralPolynomial φ n +
            Complex.sqrt
              (physicalFourier (toPotPair φ).1 (-n) *
               physicalFourier (toPotPair φ).2 n) + eplus n,
         spectralPolynomial φ n -
            Complex.sqrt
              (physicalFourier (toPotPair φ).1 (-n) *
               physicalFourier (toPotPair φ).2 n) + eminus n}

end
end NlsGge.ThirdConsultation.KSPS
