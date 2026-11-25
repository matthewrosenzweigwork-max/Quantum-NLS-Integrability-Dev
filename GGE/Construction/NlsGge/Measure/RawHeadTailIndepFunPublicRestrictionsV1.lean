import NlsGge.Measure.RawHeadTailIndepFunActualProofV6

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section

namespace NlsGge.Measure.RawHeadTailIndepFunPublicRestrictionsV1

/-- Public interface for independence of the actual raw coordinate restrictions
onto an arbitrary set of indices and its complement. -/
lemma fullWeightSequenceGaussian_indepFun_coordinateRestrictions_v1
    (c : ℕ → ℝ) (A : Set ℤ) [DecidablePred (· ∈ A)] :
    ProbabilityTheory.IndepFun
      (fun z : ℤ → ℂ => fun a : A => z a.1)
      (fun z : ℤ → ℂ => fun i : (Aᶜ : Set ℤ) => z i.1)
      (fullWeightSequenceGaussian c) := by
  exact NlsGge.Measure.RawHeadTailIndepFunActualProofV6.fullWeightSequenceGaussian_indepFun_restrict_complement_v6 c A

#check @fullWeightSequenceGaussian_indepFun_coordinateRestrictions_v1

end NlsGge.Measure.RawHeadTailIndepFunPublicRestrictionsV1
