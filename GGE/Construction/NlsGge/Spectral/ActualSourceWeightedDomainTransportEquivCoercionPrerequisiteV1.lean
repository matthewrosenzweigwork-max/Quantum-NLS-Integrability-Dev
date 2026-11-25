import NlsGge.Schur.PhysicalSector

set_option autoImplicit false

namespace NlsGge.Schur

/-- The source-pair linear-isometry inverse, viewed through its pinned linear
-equivalence representation, has the expected exact evaluation. This is the
coercion bridge needed by the source-domain transported left-inverse proof. -/
theorem sourcePairRepr_toLinearEquiv_apply_symm
    (n : ℤ) (x : SectorSquare n) :
    (sourcePairRepr n).toLinearEquiv ((sourcePairRepr n).symm x) = x := by
  change (sourcePairRepr n).toLinearEquiv
    ((sourcePairRepr n).toLinearEquiv.symm x) = x
  exact (sourcePairRepr n).toLinearEquiv.apply_symm_apply x

end NlsGge.Schur
