import NlsGge.Schur.PhysicalSector
import NlsGge.Spectral.ActualSourceWeightedDomainTransportBridgeV4

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace NlsGge.Schur

/-- The inverse of the actual source-pair isometry preserves addition on the
actual sector and source Hilbert carriers. The explicit linear-equivalence
view avoids inference through the ambient Lp dictionaries. -/
theorem sourcePairRepr_symm_map_add_actual (n : ℤ)
    (x z : SectorSquare n) :
    (sourcePairRepr n).symm (x + z) =
      (sourcePairRepr n).symm x + (sourcePairRepr n).symm z := by
  change (sourcePairRepr n).toLinearEquiv.symm (x + z) =
    (sourcePairRepr n).toLinearEquiv.symm x +
      (sourcePairRepr n).toLinearEquiv.symm z
  exact (sourcePairRepr n).toLinearEquiv.symm.map_add x z

/-- The inverse of the actual source-pair isometry preserves complex scalar
multiplication on the actual sector and source Hilbert carriers. -/
theorem sourcePairRepr_symm_map_smul_actual (n : ℤ)
    (a : ℂ) (x : SectorSquare n) :
    (sourcePairRepr n).symm (a • x) =
      a • (sourcePairRepr n).symm x := by
  change (sourcePairRepr n).toLinearEquiv.symm (a • x) =
    a • (sourcePairRepr n).toLinearEquiv.symm x
  exact (sourcePairRepr n).toLinearEquiv.symm.map_smul a x

end NlsGge.Schur

end
