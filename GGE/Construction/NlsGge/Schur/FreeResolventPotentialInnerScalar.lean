import NlsGge.Schur.FreeResolventPotentialBlocks

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The scalar action on the right argument of the actual paired-space inner
product, with all arguments explicit for use in the DVD entry proof. -/
theorem parityPair_inner_smul_right (n : ℤ) (x y : ParityPair n) (a : ℂ) :
    inner ℂ x (a • y) = a * inner ℂ x y := by
  exact inner_smul_right x y a

end NlsGge.Schur
