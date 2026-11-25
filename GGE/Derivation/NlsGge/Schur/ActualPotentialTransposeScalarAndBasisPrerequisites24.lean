import NlsGge.Schur.ActualPairTransposeTransportAfterCoordinatePrerequisite23
import NlsGge.Schur.CoveredH1ParityPairEntriesFromAE
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The scalar coordinate pairing used when extracting a coefficient from a
single-coordinate vector. -/
theorem actualPotentialTranspose_inner_one_left24 (z : ℂ) :
    inner ℂ (1 : ℂ) z = z := by
  simp only [RCLike.inner_apply, starRingEnd_apply]
  simp

/-- The inverse Fourier representative of a paired coordinate vector is the
corresponding actual single-coordinate vector. -/
theorem actualPotentialTranspose_repr_symm_single24
    (n : ℤ) (i : Bool × Sector n) :
    (parityPairRepr n).symm (lp.single 2 i (1 : ℂ)) = parityPairVector n i := by
  apply (parityPairRepr n).injective
  simp only [(parityPairRepr n).apply_symm_apply, parityPairRepr_vector]

end NlsGge.Schur
