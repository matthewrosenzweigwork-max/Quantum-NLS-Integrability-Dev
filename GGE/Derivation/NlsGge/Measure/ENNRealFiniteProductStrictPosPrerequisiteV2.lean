import Mathlib.Basic.ENNReal.BigOperators

set_option autoImplicit false
open scoped ENNReal BigOperators

namespace NlsGge.Measure.ENNRealFiniteProductStrictPosPrerequisiteV2

/-- A finite product of strictly positive extended nonnegative reals is
strictly positive, proved via the pinned nonzero-product API. -/
lemma finset_prod_pos {ι : Type*} (S : Finset ι) (f : ι → ℝ≥0∞)
    (hf : ∀ i ∈ S, 0 < f i) :
    0 < ∏ i ∈ S, f i := by
  change (⊥ : ℝ≥0∞) < ∏ i ∈ S, f i
  rw [bot_lt_iff_ne_bot]
  have hne : (∏ i ∈ S, f i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => (hf i hi).ne')
  simpa using hne

#check @finset_prod_pos

end NlsGge.Measure.ENNRealFiniteProductStrictPosPrerequisiteV2
