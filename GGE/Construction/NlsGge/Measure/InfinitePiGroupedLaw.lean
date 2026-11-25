import NlsGge.Measure.InfinitePiGroupedDefinitions
import NlsGge.Measure.InfinitePiGroupedPrerequisites
import NlsGge.Measure.InfinitePiReindex
import Mathlib.Probability.ProductMeasure

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.Measure

/-- Reassemble the actual product law of source coordinates on `A ⊕ Aᶜ`
from the separately verified reindex and curry pushforward identities. This is
only a regrouped joint-law identity; it asserts neither independence nor full
support. -/
lemma fullWeightSequenceGaussian_sumGroupedLaw_afterPrerequisites_v4
    (c : ℕ → ℝ) (A : Set ℤ) [DecidablePred (· ∈ A)] :
    (Measure.infinitePi
      (fun u : A ⊕ (Aᶜ : Set ℤ) =>
        complexGaussian (fullWeightRate c (Equiv.Set.sumCompl A u)))).map
      (BoolSigmaProbe2.actualSigmaGroupedEquiv A) =
        BoolSigmaProbe2.actualSigmaGroupedLaw c A := by
  have hSourceFamily :
      (fun u : A ⊕ (Aᶜ : Set ℤ) =>
        BoolSigmaProbe2.actualSigmaGaussianFamily c A
          (BoolSigmaProbe2.sumToBoolSigma A u)) =
      (fun u : A ⊕ (Aᶜ : Set ℤ) =>
        complexGaussian (fullWeightRate c (Equiv.Set.sumCompl A u))) := by
    funext u
    simp [BoolSigmaProbe2.actualSigmaGaussianFamily,
      BoolSigmaProbe2.sumToBoolSigma]
  rw [← hSourceFamily]
  change (Measure.infinitePi
      (fun u : A ⊕ (Aᶜ : Set ℤ) =>
        BoolSigmaProbe2.actualSigmaGaussianFamily c A
          (BoolSigmaProbe2.sumToBoolSigma A u))).map
      ((BoolSigmaProbe2.actualSigmaPiCurry A) ∘
        (BoolSigmaProbe2.actualSigmaPiReindex A)) = _
  rw [← Measure.map_map
    (BoolSigmaProbe2.actualSigmaPiCurry A).measurable
    (BoolSigmaProbe2.actualSigmaPiReindex A).measurable]
  rw [NlsGge.Measure.BoolSigmaLawPrerequisites3.actualSigmaPiReindex_map_v3]
  exact NlsGge.Measure.BoolSigmaLawPrerequisites3.actualSigmaPiCurry_map_v3 c A

end NlsGge.Measure
