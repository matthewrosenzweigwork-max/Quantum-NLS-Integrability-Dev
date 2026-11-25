import NlsGge.Schur.FreeResolventPotentialBlocks

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The resonant projection on the paired Fourier basis is the literal
coordinate mask at the actual signed resonant index. -/
theorem resonantParityPair_apply_basis (n : ℤ) (i : Bool × Sector n) :
    resonantParityPair n (parityPairVector n i) =
      if i.2 = resonantIndex n then parityPairVector n i else 0 := by
  apply (parityPairRepr n).injective
  apply lp.ext
  funext j
  by_cases hres : i.2 = resonantIndex n <;>
    by_cases hji : j = i <;>
      simp [resonantParityPair, resonantSquare_apply, hres,
        parityPairRepr_vector, lp.single_apply, hji]

end NlsGge.Schur
