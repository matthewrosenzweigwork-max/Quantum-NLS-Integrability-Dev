import Mathlib
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST027
import NlsGge.ThirdConsultation.KST.KST032Host

/- KST034Host PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST034Host.lean.
   SUPPORTING host module (no packet increment).  Bodies VERBATIM from the design DEFINITIONS/KST.lean.md
   (gpt6pro_followup10; Pro rounds 7-12 do not touch them), section "One concrete adapted Fourier map on all weights":
   RawPair (:351), rawFourier (:353), weightedCoeffs (:387), weightedLift (:403), adaptedCoefficients (:421),
   adaptedFourier (:426).  None of these is defined in NlsGge (grep) nor in another worker's candidate (grep).
   NOT hosted here (not needed by KST-034): rawEnergy, adaptedCutoffCondition, adaptedThreshold, adaptedInverse, ...
   Already landed and imported, NOT redeclared: weightFact / Weighted / weightedPotential (KST027), diagonalZero (KST032Host),
   b / c / center (KST018), Potential (DM004 via KST018), periodOneWeight (KST002).
   NOTE: `NlsGge.ThirdConsultation.DM.RawPair` (DM014) is the same abbreviation in another namespace; the design places it in
   NlsGge.ThirdConsultation.KST, so it is declared here (different full name, no clash unless both namespaces are opened).
   LEXICAL REPAIR (elaboration only): attribute [local instance] Classical.propDecidable for the dite in weightedLift
   (same repair as KST031Host / KST032Host). -/
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

abbrev RawPair := Bool → ℤ → ℂ

def rawFourier (φ : Potential) : RawPair :=
  fun channel m => physicalFourier (φ channel) m

def weightedCoeffs (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (x : Weighted ω) : RawPair := fun channel m => x channel m

def weightedLift (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] (r : RawPair) : Weighted ω :=
  if h : ∃ x : Weighted ω, weightedCoeffs ω x = r then Classical.choose h else 0

def adaptedCoefficients (N : ℕ) (φ : Potential) : RawPair :=
  fun channel m => if m.natAbs ≤ N then rawFourier φ channel m
    else if channel then c φ (-m) (diagonalZero (-m) φ)
    else b φ m (diagonalZero m φ)

def adaptedFourier (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] (N : ℕ)
    (x : Weighted ω) : Weighted ω :=
  weightedLift ω (adaptedCoefficients N (weightedPotential ω hω x))

end NlsGge.ThirdConsultation.KST
end
