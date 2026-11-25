import Mathlib
import NlsGge.ThirdConsultation.G3.G3003Host
import NlsGge.GK38.Lib.EntireProductsC34b

/- G3-026 HOST (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/ThirdConsultation/G3/G3026Host.lean, namespace NlsGge.GKDefinitionDesign (as G3003Host, G3010Host, G3028Host).
   Hosts the design names `fixedIndexReciprocalTail` and `betaPartialSum`, bodies VERBATIM from DEFINITIONS/G3.lean.md "Series and tails"
   (gpt6pro_followup8; byte-identical in followup7).  `spectralNorm` of the same block is hosted by proof development's G3028Host, not here.
   grep NlsGge/ and Armstrong/ (2026-10-31): neither name is defined elsewhere.  Lib.c3w is NlsGge.GK38.Lib.EntireProductsC34b (reached
   through `open NlsGge.GK38`; imported explicitly), offDiagonalBeta is G3003Host.
   Shared host: G3-026, G3-027 and later G3 packets import this module and must not redeclare these names. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def fixedIndexReciprocalTail (n : ℤ) (R : ℕ) : ℝ :=
  Real.sqrt (∑' m : ℤ, if (R : ℝ) < |(m : ℝ)| then Lib.c3w n m ^ 2 else 0)

def betaPartialSum (n : ℤ) (R : ℕ) (φ : PotPair) : ℂ :=
  ∑ m ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), offDiagonalBeta n m φ

end
end NlsGge.GKDefinitionDesign
