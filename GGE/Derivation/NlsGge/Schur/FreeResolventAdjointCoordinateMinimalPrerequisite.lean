import NlsGge.Schur.FreeResolventPotentialVectorNormPrerequisites

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

/-- Exact coordinate identity for the actual adjoint on the actual paired
Fourier basis. It isolates complex inner-product conjugation from the four
resonant norm estimates. -/
theorem parityPair_adjoint_repr_coordinate_prerequisite
    (n : ℤ) (T : ParityPair n →L[ℂ] ParityPair n)
    (i j : Bool × Sector n) :
    parityPairRepr n (T.adjoint (parityPairVector n j)) i =
      star (inner ℂ (parityPairVector n j) (T (parityPairVector n i))) := by
  letI : InnerProductSpace ℂ (ParityPair n) :=
    PiLp.innerProductSpace (𝕜 := ℂ) (ι := Bool)
      (f := fun _ : Bool => scalarParity n)
  have hAdj := ContinuousLinearMap.adjoint_inner_left T
    (parityPairVector n i) (parityPairVector n j)
  calc
    parityPairRepr n (T.adjoint (parityPairVector n j)) i =
        inner ℂ (parityPairVector n i) (T.adjoint (parityPairVector n j)) :=
      parityPairRepr_inner n (T.adjoint (parityPairVector n j)) i
    _ = star (inner ℂ (T.adjoint (parityPairVector n j))
        (parityPairVector n i)) :=
      (inner_conj_symm (parityPairVector n i)
        (T.adjoint (parityPairVector n j))).symm
    _ = star (inner ℂ (parityPairVector n j)
        (T (parityPairVector n i))) := congrArg star hAdj

end NlsGge.Schur
