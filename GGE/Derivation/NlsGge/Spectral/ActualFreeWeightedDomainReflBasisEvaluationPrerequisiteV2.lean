import NlsGge.Schur.FreeDomainPointwise
import NlsGge.Schur.PhysicalSector

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The inverse of the reflexive linear isometry equivalence acts as the
identity on the actual sector Hilbert space. This isolates the basis-vector
evaluation needed by the weighted-domain density proof. -/
theorem sectorLinearIsometryRefl_symm_apply (n : ℤ)
    (x : SectorSquare n) :
    (LinearIsometryEquiv.refl ℂ (SectorSquare n)).symm x = x := by
  change ((LinearIsometryEquiv.refl ℂ (SectorSquare n)).toLinearEquiv).symm x = x
  rw [LinearIsometryEquiv.toLinearEquiv_refl,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply]

end NlsGge.Schur

end
