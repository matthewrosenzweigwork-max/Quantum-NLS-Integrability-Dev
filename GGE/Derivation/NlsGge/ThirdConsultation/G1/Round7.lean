import Mathlib
import NlsGge.ThirdConsultation.G1.Round5

/- G1-035 HOST (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/G1/Round7.lean.
   Bodies verbatim from DEFINITIONS/G1.lean.md (gpt6pro_followup4) for wkbPartial, wkbResidual, wkbResidualTail.
   LEXICAL REPAIR: spectral parameter renamed λ -> l (Lean keyword); inner tail index l renamed j (no shadowing).
   Round5 supplies wkbR, weakDerivative, physicalProduct. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

def wkbPartial (N : ℕ) (l : ℂ) (φ : PotPair) : PhysicalL2 :=
  ∑ n ∈ Finset.Icc 1 N, ((2*Complex.I*l)^n)⁻¹ • wkbR φ n

def wkbResidual (N : ℕ) (l : ℂ) (φ : PotPair) : PhysicalL2 :=
  weakDerivative (wkbPartial N l φ) -
    (2*Complex.I*l) • wkbPartial N l φ +
    physicalProduct φ.1
      (physicalProduct (wkbPartial N l φ) (wkbPartial N l φ)) - φ.2

def wkbResidualTail (N : ℕ) (l : ℂ) (φ : PotPair) : PhysicalL2 :=
  ((2*Complex.I*l)^N)⁻¹ • weakDerivative (wkbR φ N) +
    ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
      if N ≤ k+j then ((2*Complex.I*l)^(k+j))⁻¹ •
        physicalProduct φ.1 (physicalProduct (wkbR φ k) (wkbR φ j))
      else 0

end NlsGge.GKDefinitionDesign
end
