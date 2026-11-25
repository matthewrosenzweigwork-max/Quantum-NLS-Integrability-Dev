import NlsGge.Schur.FreeResolventPotentialBlocks

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- Exact right-associated scalar action appearing after the actual paired
free-resolvent basis evaluations. -/
theorem actualCenterShiftRightAssociatedVectorActionPrerequisiteV1_25
    (n : ℤ) (a b c d : ℂ) (x : ParityPair n) :
    a • x + (b * (c * d)) • x = (a + b * (c * d)) • x := by
  exact (add_smul a (b * (c * d)) x).symm

end NlsGge.Schur
