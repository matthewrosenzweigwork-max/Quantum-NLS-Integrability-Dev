import Mathlib
import NlsGge.Atomic.G2.G2021
import NlsGge.Atomic.G2.G2046
import NlsGge.ThirdConsultation.G2.G2072Host

/- G3-005 BANK HOST (proof development, AUTHOR; not self-reviewed). Target NlsGge/ThirdConsultation/G3/G3005Host.lean (name proposed).
   Bodies VERBATIM from root/gpt6pro_followup7 DEFINITIONS/G3.lean.md (definitions_design_20261027), betaGapDensity and
   betaGapIntegral (lines 68-76). Shared host: proof development's G3005_SUPPORT_INTEG01 redeclares betaGapDensity and must
   import this module instead. No other names declared. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def betaGapDensity (n m : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  let z := lamMinus φ m + (t : ℂ) * gap φ m
  psi n φ z * gap φ m /
    (2 * Complex.I * (-Complex.I * gap φ m *
      (Real.sqrt (t*(1-t)) : ℂ)) * rootProduct m (φ,z))

def betaGapIntegral (n m : ℤ) (φ : PotPair) : ℂ :=
  ∫ t in (0 : ℝ)..1, betaGapDensity n m φ t

end
end NlsGge.GKDefinitionDesign
