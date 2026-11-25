import Mathlib
import NlsGge.ThirdConsultation.G3.G3003Host
import NlsGge.GK38.Lib.EntireProductsC34b
import Armstrong.Work.RawBetaSumSpectralMass

/- G3-028 HOST (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/ThirdConsultation/G3/G3028Host.lean, namespace NlsGge.GKDefinitionDesign (as G3003Host, G3006Host, G3010Host).
   Hosts the design names `spectralNorm`, `spectralTailNorm`, `reciprocalSquareTail`, `nearDiagonalBetaNorm`, `farDiagonalBetaNorm`, bodies VERBATIM
   from DEFINITIONS/G3.lean.md "Series and tails" (gpt6pro_followup8; byte-identical in followup7).  `spectralNorm` is hosted too because the G3-029
   head uses it.  `fixedIndexReciprocalTail` and `betaPartialSum` of the same design block are NOT hosted (G3-026/027 own them).
   grep NlsGge/, Armstrong/ and all worker folders (2026-10-31): none of these names is defined elsewhere.
   gk151BetaMass38 is Armstrong.Work.RawBetaSumSpectralMass (X-006 closure line 86), Lib.c3w is NlsGge.GK38.Lib.EntireProductsC34b,
   offDiagonalBeta is G3003Host.  Shared host: G3-028, G3-029 (and later G3-026/027/030) import this module and must not redeclare these names. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def spectralNorm (φ : PotPair) : ℝ :=
  Real.sqrt (∑' m : ℤ, ‖gk151BetaMass38 φ m‖^2)

def spectralTailNorm (φ : PotPair) (R : ℝ) : ℝ :=
  Real.sqrt (∑' m : ℤ, if R ≤ |(m : ℝ)| then ‖gk151BetaMass38 φ m‖^2 else 0)

def reciprocalSquareTail (R : ℝ) : ℝ :=
  Real.sqrt (∑' k : ℤ, if R < |(k : ℝ)| then Lib.c3w 0 k ^ 2 else 0)

def nearDiagonalBetaNorm (n : ℤ) (φ : PotPair) (m : ℤ) : ℝ :=
  if 0 < |(m : ℝ)-n| ∧ |(m : ℝ)-n| ≤ |(n : ℝ)|/2
  then ‖offDiagonalBeta n m φ‖ else 0

def farDiagonalBetaNorm (n : ℤ) (φ : PotPair) (m : ℤ) : ℝ :=
  if |(n : ℝ)|/2 < |(m : ℝ)-n| then ‖offDiagonalBeta n m φ‖ else 0

end
end NlsGge.GKDefinitionDesign
