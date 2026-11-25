import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false
set_option pp.maxSteps 10000000
open scoped ENNReal

namespace NlsGge.Measure.WeightedGaussianOmittedTsumPrerequisiteV1

/-- Reindex a full nonnegative ENNReal sum over a set containing the support
onto the corresponding subtype. -/
lemma tsum_eq_subtype_of_support_subset
    (S : Set ℤ) (f : ℤ → ℝ≥0∞)
    (hsupp : Function.support f ⊆ S) :
    (∑' n : ℤ, f n) = ∑' n : S, f n.1 :=
  (tsum_subtype_eq_of_support_subset hsupp).symm

#check @tsum_eq_subtype_of_support_subset

end NlsGge.Measure.WeightedGaussianOmittedTsumPrerequisiteV1
