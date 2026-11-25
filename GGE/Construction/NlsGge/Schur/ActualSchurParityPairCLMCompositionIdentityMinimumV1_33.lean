import NlsGge.Schur.ActualComplementaryQVDJointInverseAndEqualDiagonalV5_30

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The actual algebra-one continuous linear map is the identity for both
composition sides on the concrete signed parity-pair carrier. This isolates
the carrier/dictionary identity needed by the resolvent cancellation proof. -/
theorem actualSchurParityPairCLMCompositionIdentityMinimumV1_33
    (n : ℤ) (A : ParityPair n →L[ℂ] ParityPair n) :
    A.comp (1 : ParityPair n →L[ℂ] ParityPair n) = A ∧
      (1 : ParityPair n →L[ℂ] ParityPair n).comp A = A := by
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    rfl
  · apply ContinuousLinearMap.ext
    intro x
    rfl

end NlsGge.Schur
