import NlsGge.Schur.FreeCoordinateDomainInverse
import NlsGge.Spectral.ActualFullImaginaryFreeSourceResolventV3
import NlsGge.Schur.PhysicalSector
import NlsGge.Spectral.ActualSourceWeightedDomainTransportEquivCoercionPrerequisiteV1

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
namespace TransportBridgeV4
open NlsGge.Pilot

private def sourcePairReprLinearMap (n : ℤ) :
    SourcePairL2 →ₗ[ℂ] SectorSquare n :=
  (sourcePairRepr n).toLinearEquiv.toLinearMap

private def sourcePairReprSymmLinearMap (n : ℤ) :
    SectorSquare n →ₗ[ℂ] SourcePairL2 :=
  (sourcePairRepr n).toLinearEquiv.symm.toLinearMap

/-- The actual source-space domain is the pullback of the weighted-coordinate
domain under the pinned source-pair linear isometry. -/
def recoveredActualSourceFreeWeightedDomain (n : ℤ) : Submodule ℂ SourcePairL2 where
  carrier := {x | sourcePairReprLinearMap n x ∈ freeWeightedDomainPointwise n}
  zero_mem' := by
    change sourcePairReprLinearMap n 0 ∈ freeWeightedDomainPointwise n
    simp
  add_mem' := by
    intro x z hx hz
    change sourcePairReprLinearMap n (x + z) ∈ freeWeightedDomainPointwise n
    rw [(sourcePairReprLinearMap n).map_add]
    exact (freeWeightedDomainPointwise n).add_mem hx hz
  smul_mem' := by
    intro a x hx
    change sourcePairReprLinearMap n (a • x) ∈ freeWeightedDomainPointwise n
    rw [(sourcePairReprLinearMap n).map_smul]
    exact (freeWeightedDomainPointwise n).smul_mem a hx

private def recoveredActualSourceSequenceMap (n : ℤ) :
    recoveredActualSourceFreeWeightedDomain n →ₗ[ℂ] freeWeightedDomainPointwise n where
  toFun x := ⟨sourcePairReprLinearMap n x, x.property⟩
  map_add' x z := by
    apply Subtype.ext
    exact (sourcePairReprLinearMap n).map_add x z
  map_smul' a x := by
    apply Subtype.ext
    exact (sourcePairReprLinearMap n).map_smul a x

/-- The actual source weighted free operator, with no boundedness claim in the
ambient source L² norm. -/
def recoveredActualSourceFreeShiftedDirac (n : ℤ) (z : ℂ) :
    recoveredActualSourceFreeWeightedDomain n →ₗ[ℂ] SourcePairL2 :=
  (sourcePairReprSymmLinearMap n).comp
    ((freeShiftedCoordinateDirac n z).comp (recoveredActualSourceSequenceMap n))

theorem recoveredActualSourceFreeShiftedDirac_repr_apply
    (n : ℤ) (z : ℂ) (x : recoveredActualSourceFreeWeightedDomain n) :
    sourcePairRepr n (recoveredActualSourceFreeShiftedDirac n z x) =
      freeShiftedCoordinateDirac n z ⟨sourcePairRepr n x, x.property⟩ := by
  change (sourcePairRepr n).toLinearEquiv
      ((sourcePairRepr n).toLinearEquiv.symm
        (freeShiftedCoordinateDirac n z
          ⟨(sourcePairRepr n).toLinearEquiv x, x.property⟩)) = _
  exact (sourcePairRepr n).toLinearEquiv.apply_symm_apply _

/-- The all-mode free resolvent, transported to the exact source weighted
domain subtype. -/
def recoveredActualSourceFullImaginaryResolventDomain
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SourcePairL2) :
    recoveredActualSourceFreeWeightedDomain n :=
  ⟨(sourcePairRepr n).symm
      (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x)), by
    change sourcePairReprLinearMap n ((sourcePairRepr n).symm
      (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x))) ∈
      freeWeightedDomainPointwise n
    change (sourcePairRepr n).toLinearEquiv
      ((sourcePairRepr n).toLinearEquiv.symm
        (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x))) ∈ _
    rw [(sourcePairRepr n).toLinearEquiv.apply_symm_apply]
    exact sourceFullImaginaryResolventSquare_mem_freeWeightedDomain n y hy
      (sourcePairRepr n x)⟩

/-- The source-domain left-inverse identity after transport. This isolates the
coercion-sensitive step without making any range or surjectivity claim. -/
theorem recoveredActualSourceFullResolvent_left_inverse_on_domain
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y)
    (x : recoveredActualSourceFreeWeightedDomain n) :
    recoveredActualSourceFullImaginaryResolventDomain n y hy
      (recoveredActualSourceFreeShiftedDirac n (Complex.I * (y : ℂ)) x) = x := by
  apply Subtype.ext
  apply (sourcePairRepr n).toLinearEquiv.injective
  simp only [recoveredActualSourceFullImaginaryResolventDomain]
  rw [recoveredActualSourceFreeShiftedDirac_repr_apply]
  calc
    (sourcePairRepr n).toLinearEquiv
        ((sourcePairRepr n).toLinearEquiv.symm
          (sourceFullImaginaryResolventSquare n y hy
            (freeShiftedCoordinateDirac n (Complex.I * (y : ℂ))
              ⟨(sourcePairRepr n).toLinearEquiv x, x.property⟩))) =
      sourceFullImaginaryResolventSquare n y hy
        (freeShiftedCoordinateDirac n (Complex.I * (y : ℂ))
          ⟨(sourcePairRepr n).toLinearEquiv x, x.property⟩) :=
        sourcePairRepr_toLinearEquiv_apply_symm n _
    _ = (sourcePairRepr n).toLinearEquiv x :=
      sourceFullImaginaryResolventSquare_left_inverse n y hy
        ⟨(sourcePairRepr n).toLinearEquiv x, x.property⟩

end TransportBridgeV4
end NlsGge.Schur

end
