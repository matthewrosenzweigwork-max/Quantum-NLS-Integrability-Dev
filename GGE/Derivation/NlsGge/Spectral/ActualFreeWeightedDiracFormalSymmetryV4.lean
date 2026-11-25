import NlsGge.Schur.FreeCoordinateDomainInverse
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import NlsGge.Spectral.ActualSpectralCenterStarRingInnerBalanceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace NlsGge.Schur

/-- The actual unbounded free diagonal, represented as a partial linear map
with its genuine weighted `ℓ²` domain. -/
def actualFreeWeightedDiracPMap (n : ℤ) :
    SectorSquare n →ₗ.[ℂ] SectorSquare n :=
  ⟨freeWeightedDomainPointwise n, freeCoordinateDirac n⟩

/-- The fixed-sector free diagonal is formally symmetric on its actual domain.
This is only the inner-product identity on domain vectors; it does not assert
equality with the adjoint or either resolvent-range condition. -/
theorem actualFreeWeightedDirac_formalSelfAdjoint (n : ℤ) :
    (actualFreeWeightedDiracPMap n).IsFormalAdjoint
      (actualFreeWeightedDiracPMap n) := by
  intro x y
  change inner ℂ (freeCoordinateDirac n x) (y : SectorSquare n) =
    inner ℂ (x : SectorSquare n) (freeCoordinateDirac n y)
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr ?_
  intro i
  rw [freeCoordinateDirac_apply, freeCoordinateDirac_apply]
  calc
    inner ℂ (spectralCenter i.2.val • ((x : SectorSquare n) i))
        ((y : SectorSquare n) i) =
        star (spectralCenter i.2.val) *
          inner ℂ ((x : SectorSquare n) i) ((y : SectorSquare n) i) := by
      simpa only [inner_smul_left, starRingEnd_apply]
    _ = inner ℂ ((x : SectorSquare n) i)
          (spectralCenter i.2.val • ((y : SectorSquare n) i)) := by
      exact spectralCenter_starRingEnd_inner_balance n i.2
        ((x : SectorSquare n) i) ((y : SectorSquare n) i)

end NlsGge.Schur

end
