import NlsGge.Schur.RootActualSchurQVDInverseHasFDerivAtActualParentMinimum36V4
set_option autoImplicit false
noncomputable section
namespace NlsGge.Schur
/-- The two actual printed complex self-module parents, isolated from the
resolvent derivative proof. No derivative conclusion is assumed here. -/
theorem complexCanonicalSelfModuleAgreement36MinimumV1 :
    (CommCStarAlgebra.toNonUnitalCommCStarAlgebra ℂ).toNonUnitalCStarAlgebra.toModule =
      (Semiring.toModule : Module ℂ ℂ) := by
  rfl
end NlsGge.Schur
end
