import NlsGge.Measure.RawHeadTailIndepFunPublicRestrictionsV1

set_option autoImplicit false

namespace NlsGge.Measure.WeightedGaussianHeadRestrictionIdentityV2

private def finiteHeadRestriction (S : Finset ℤ) (z : ℤ → ℂ) : (i : S) → ℂ :=
  fun i => z i.1

/-- The finite head map is exactly the public coordinate restriction used by
actual raw-product independence. -/
lemma finiteHeadRestriction_eq_public (S : Finset ℤ) :
    (fun z : ℤ → ℂ => finiteHeadRestriction S z) =
      (fun z => fun i : (S : Set ℤ) => z i.1) := rfl

#check @finiteHeadRestriction_eq_public

end NlsGge.Measure.WeightedGaussianHeadRestrictionIdentityV2
