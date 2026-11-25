import NlsGge.Schur.SourceReflectedIntervalFourierNetV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.Schur

/-- The forward representation sends the actual interval pair into its
sector coordinates, whose source components recover the original pair. -/
theorem sourceCoordinateComponent_sourcePairRepr
    (n : ℤ) (P : SourcePairL2) (b : Bool) :
    sourceCoordinateComponent n (sourcePairRepr n P) b = P b := by
  change scalarParityRestrict n
    ((parityPairRepr n).symm
      ((parityPairRepr n) ((parityPairIntervalEquiv n).symm P)) b) = _
  rw [(parityPairRepr n).symm_apply_apply]
  change scalarParityIntervalEquiv n
    ((scalarParityIntervalEquiv n).symm (P b)) = P b
  exact (scalarParityIntervalEquiv n).apply_symm_apply _

end NlsGge.Schur
end
