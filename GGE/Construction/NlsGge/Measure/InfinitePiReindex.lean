import NlsGge.Measure.CountableGaussian
import Mathlib.Probability.ProductMeasure

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.Measure

/-- Reindex the actual raw countable Gaussian product by the partition of `ℤ` into
`A` and its set complement. The complement is explicitly a set to avoid Lean
parsing it as a type complement. This is only the reindexing step; it does not
assert that the pushed-forward split map has a product law. -/
lemma fullWeightSequenceGaussian_reindex_sumCompl_v2
    (c : ℕ → ℝ) (A : Set ℤ) [DecidablePred (· ∈ A)] :
    (Measure.infinitePi
      (fun u : A ⊕ (Aᶜ : Set ℤ) =>
        complexGaussian (fullWeightRate c (Equiv.Set.sumCompl A u)))).map
      (MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℂ) (Equiv.Set.sumCompl A)) =
        fullWeightSequenceGaussian c := by
  rw [fullWeightSequenceGaussian, countableComplexGaussian]
  exact Measure.infinitePi_map_piCongrLeft (X := fun _ : ℤ => ℂ)
    (μ := fun n : ℤ => complexGaussian (fullWeightRate c n)) (Equiv.Set.sumCompl A)

end NlsGge.Measure
