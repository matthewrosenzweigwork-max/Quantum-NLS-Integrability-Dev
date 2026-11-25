import NlsGge.Measure.InfinitePiGroupedDefinitions
import Mathlib.Probability.ProductMeasure

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.Measure.BoolSigmaLawPrerequisites3

/-- The wrapped actual Gaussian coordinate family is a probability family. This
is discharged by unfolding to the project's pinned `complexGaussian_probability`
instance; it adds no hypothesis to the product-law statements. -/
lemma actualSigmaGaussianFamily_isProbability_v3
    (c : ℕ → ℝ) (A : Set ℤ) [DecidablePred (· ∈ A)] :
    ∀ p : BoolSigmaProbe2.BoolSumIndex A,
      IsProbabilityMeasure (BoolSigmaProbe2.actualSigmaGaussianFamily c A p) := by
  intro p
  unfold BoolSigmaProbe2.actualSigmaGaussianFamily
  infer_instance

/-- Reindex the sum-indexed source-coordinate Gaussian law to the Bool-Sigma
indexed Gaussian family. The wrapper is changed to the exact pinned
`piCongrLeft` map before applying `infinitePi_map_piCongrLeft`. -/
lemma actualSigmaPiReindex_map_v3
    (c : ℕ → ℝ) (A : Set ℤ) [DecidablePred (· ∈ A)] :
    (Measure.infinitePi
      (fun u : A ⊕ (Aᶜ : Set ℤ) =>
        BoolSigmaProbe2.actualSigmaGaussianFamily c A
          (BoolSigmaProbe2.sumToBoolSigma A u))).map
      (BoolSigmaProbe2.actualSigmaPiReindex A) =
        Measure.infinitePi (BoolSigmaProbe2.actualSigmaGaussianFamily c A) := by
  letI : ∀ p : BoolSigmaProbe2.BoolSumIndex A,
      IsProbabilityMeasure (BoolSigmaProbe2.actualSigmaGaussianFamily c A p) :=
    actualSigmaGaussianFamily_isProbability_v3 c A
  change (Measure.infinitePi
      (fun u : A ⊕ (Aᶜ : Set ℤ) =>
        BoolSigmaProbe2.actualSigmaGaussianFamily c A
          (BoolSigmaProbe2.sumToBoolSigma A u))).map
      (MeasurableEquiv.piCongrLeft
        (fun _ : BoolSigmaProbe2.BoolSumIndex A => ℂ)
        (BoolSigmaProbe2.sumToBoolSigma A)) =
        Measure.infinitePi (BoolSigmaProbe2.actualSigmaGaussianFamily c A)
  exact Measure.infinitePi_map_piCongrLeft
    (X := fun _ : BoolSigmaProbe2.BoolSumIndex A => ℂ)
    (μ := BoolSigmaProbe2.actualSigmaGaussianFamily c A)
    (BoolSigmaProbe2.sumToBoolSigma A)

/-- Curry the reindexed Sigma-indexed Gaussian law to its actual nested Bool
block law. The local `∀ b j` probability instance is derived from the same
actual-coordinate Gaussian probability instance, then the wrapper is changed
to the exact pinned `piCurry` map before applying `infinitePi_map_piCurry`. -/
lemma actualSigmaPiCurry_map_v3
    (c : ℕ → ℝ) (A : Set ℤ) [DecidablePred (· ∈ A)] :
    (Measure.infinitePi (BoolSigmaProbe2.actualSigmaGaussianFamily c A)).map
      (BoolSigmaProbe2.actualSigmaPiCurry A) =
        BoolSigmaProbe2.actualSigmaGroupedLaw c A := by
  have hFamilyProb := actualSigmaGaussianFamily_isProbability_v3 c A
  letI : ∀ b : Bool, ∀ j : bif b then (Aᶜ : Set ℤ) else A,
      IsProbabilityMeasure
        (BoolSigmaProbe2.actualSigmaGaussianFamily c A ⟨b, j⟩) := by
    intro b j
    exact hFamilyProb ⟨b, j⟩
  unfold BoolSigmaProbe2.actualSigmaGroupedLaw
  change (Measure.infinitePi
      (BoolSigmaProbe2.actualSigmaGaussianFamily c A)).map
      (MeasurableEquiv.piCurry
        (fun b (j : bif b then (Aᶜ : Set ℤ) else A) => ℂ)) =
      Measure.infinitePi (fun b : Bool =>
        Measure.infinitePi (fun j : bif b then (Aᶜ : Set ℤ) else A =>
          BoolSigmaProbe2.actualSigmaGaussianFamily c A ⟨b, j⟩))
  exact Measure.infinitePi_map_piCurry
    (X := fun b j => ℂ)
    (fun b j => BoolSigmaProbe2.actualSigmaGaussianFamily c A ⟨b, j⟩)

end NlsGge.Measure.BoolSigmaLawPrerequisites3
