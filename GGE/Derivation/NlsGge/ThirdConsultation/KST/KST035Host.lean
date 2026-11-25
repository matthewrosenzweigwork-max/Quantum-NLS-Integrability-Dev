import Mathlib
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST034Host

/- KST035Host PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST035Host.lean.
   SUPPORTING host module (no packet increment).  Bodies VERBATIM from the design DEFINITIONS/KST.lean.md
   (gpt6pro_followup10; Pro rounds 7-12 do not touch them), section "One concrete adapted Fourier map on all weights":
   rawEnergy (:356), adaptedCutoffCondition (:443), adaptedThreshold (:450).  None of these is defined in NlsGge (grep)
   nor in another worker's candidate (grep).  Already landed/under review and imported, NOT redeclared:
   RawPair / adaptedCoefficients / rawFourier (KST034Host, proof development), physicalComponentBall / productWeight /
   diagonalThreshold (KST031Host), SecondaryWeight (KST/Basic).
   LEXICAL REPAIR (elaboration only): attribute [local instance] Classical.propDecidable for the dite/Nat.find in
   adaptedThreshold (same repair as KST031Host diagonalThreshold). -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

def rawEnergy (ω : ℤ → ℝ) (r : RawPair) : ℝ≥0∞ :=
  ∑' m : ℤ, ENNReal.ofReal
    (ω (2*m)^2 * (‖r true m‖^2 + ‖r false m‖^2))

def adaptedCutoffCondition (w : ℤ → ℝ) (M : ℝ) (N : ℕ) : Prop :=
  diagonalThreshold w M ≤ N ∧
  ∀ v : ℤ → ℝ, SecondaryWeight v →
    ∀ φ ∈ physicalComponentBall (productWeight w v) (2*M),
      rawEnergy (productWeight w v) (adaptedCoefficients N φ-rawFourier φ) ≤
        ENNReal.ofReal ((M/16)^2)

def adaptedThreshold (w : ℤ → ℝ) (M : ℝ) : ℕ :=
  if h : ∃ N : ℕ, adaptedCutoffCondition w M N then Nat.find h
  else diagonalThreshold w M

end NlsGge.ThirdConsultation.KST
end
