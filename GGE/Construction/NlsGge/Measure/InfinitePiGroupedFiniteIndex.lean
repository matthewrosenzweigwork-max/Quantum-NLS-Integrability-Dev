import NlsGge.Measure.InfinitePiGroupedDefinitions
import NlsGge.Measure.InfinitePiGroupedPrerequisites
import Mathlib.Probability.ProductMeasure

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.Measure.BoolSigmaEqPiPrerequisiteV1

abbrev Block (A : Set ℤ) (b : Bool) :=
  (j : bif b then (Aᶜ : Set ℤ) else A) → ℂ

def actualBlockLaw (c : ℕ → ℝ) (A : Set ℤ) [DecidablePred (· ∈ A)]
    (b : Bool) : Measure (Block A b) :=
  Measure.infinitePi (fun j : bif b then (Aᶜ : Set ℤ) else A =>
    BoolSigmaProbe2.actualSigmaGaussianFamily c A ⟨b, j⟩)

/-- The actual Bool-block Gaussian law is the finite outer product measure.
Its block probability and sigma-finite instances are derived from the pinned
complex-Gaussian coordinate probability; no new measure premise is added. -/
lemma actualSigmaGroupedLaw_eq_pi_v1
    (c : ℕ → ℝ) (A : Set ℤ) [DecidablePred (· ∈ A)] :
    BoolSigmaProbe2.actualSigmaGroupedLaw c A = Measure.pi (actualBlockLaw c A) := by
  have hCoordProb : ∀ p : BoolSigmaProbe2.BoolSumIndex A,
      IsProbabilityMeasure (BoolSigmaProbe2.actualSigmaGaussianFamily c A p) :=
    NlsGge.Measure.BoolSigmaLawPrerequisites3.actualSigmaGaussianFamily_isProbability_v3 c A
  letI : ∀ b : Bool, ∀ j : bif b then (Aᶜ : Set ℤ) else A,
      IsProbabilityMeasure (BoolSigmaProbe2.actualSigmaGaussianFamily c A ⟨b, j⟩) := by
    intro b j
    exact hCoordProb ⟨b, j⟩
  have hBlockProb : ∀ b : Bool, IsProbabilityMeasure (actualBlockLaw c A b) := by
    intro b
    dsimp [actualBlockLaw]
    infer_instance
  letI : ∀ b : Bool, IsProbabilityMeasure (actualBlockLaw c A b) := hBlockProb
  have hBlockSigma : ∀ b : Bool, SigmaFinite (actualBlockLaw c A b) := by
    intro b
    infer_instance
  change Measure.infinitePi (actualBlockLaw c A) = Measure.pi (actualBlockLaw c A)
  exact Measure.infinitePi_eq_pi (actualBlockLaw c A)

end NlsGge.Measure.BoolSigmaEqPiPrerequisiteV1
