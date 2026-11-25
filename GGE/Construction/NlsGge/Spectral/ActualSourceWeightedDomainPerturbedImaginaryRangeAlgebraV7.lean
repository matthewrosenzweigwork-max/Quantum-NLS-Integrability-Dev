import NlsGge.Spectral.ActualSourceWeightedDomainPotentialNegativeResolventAfterAEV3
import NlsGge.Spectral.ActualSourceWeightedDomainTransportBridgeV4
import NlsGge.Spectral.ActualVR0LargeImaginaryMinusTwoSidedInverseV2
import NlsGge.Spectral.ActualNegativeVR0LargeImaginaryMinusTwoSidedInverseV1
import NlsGge.Spectral.SourcePairReprInverseLinearityPrerequisiteV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot
open TransportBridgeV4

/-- Transport the recovered source-domain vector to its actual Fourier
weighted-domain representative. This is a linear map between the two genuine
subtypes, not a bounded map on the ambient source L² space. -/
def recoveredActualSourceWeightedDomainSequenceMapAfterAE (n : ℤ) :
    recoveredActualSourceFreeWeightedDomain n →ₗ[ℂ]
      freeWeightedDomainPointwise n where
  toFun x := ⟨(sourcePairRepr n).toLinearEquiv x, x.property⟩
  map_add' x z := by
    apply Subtype.ext
    exact (sourcePairRepr n).toLinearEquiv.map_add x z
  map_smul' a x := by
    apply Subtype.ext
    exact (sourcePairRepr n).toLinearEquiv.map_smul a x

/-- The actual positive-imaginary free resolvent as a linear map into the
recovered source weighted-domain subtype. -/
def recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) :
    SourcePairL2 →ₗ[ℂ] recoveredActualSourceFreeWeightedDomain n where
  toFun := recoveredActualSourceFullImaginaryResolventDomain n y hy
  map_add' x z := by
    apply Subtype.ext
    change (sourcePairRepr n).symm
        (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n (x + z))) =
      (sourcePairRepr n).symm
        (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x)) +
      (sourcePairRepr n).symm
        (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n z))
    rw [(sourcePairRepr n).map_add, map_add]
    exact sourcePairRepr_symm_map_add_actual n
      (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x))
      (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n z))
  map_smul' a x := by
    apply Subtype.ext
    change (sourcePairRepr n).symm
        (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n (a • x))) =
      a • (sourcePairRepr n).symm
        (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x))
    rw [(sourcePairRepr n).map_smul, map_smul]
    exact sourcePairRepr_symm_map_smul_actual n a
      (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x))

/-- The actual negative-imaginary free resolvent as a linear map into the
recovered source weighted-domain subtype. -/
def recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) :
    SourcePairL2 →ₗ[ℂ] recoveredActualSourceFreeWeightedDomain n where
  toFun x :=
    ⟨(sourcePairRepr n).symm
        (sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x)), by
      change (sourcePairRepr n).toLinearEquiv
          ((sourcePairRepr n).toLinearEquiv.symm
            (sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x))) ∈
        freeWeightedDomainPointwise n
      rw [(sourcePairRepr n).toLinearEquiv.apply_symm_apply]
      exact sourceFullNegativeImaginaryResolventSquare_mem_freeWeightedDomain n y hy
        (sourcePairRepr n x)⟩
  map_add' x z := by
    apply Subtype.ext
    change (sourcePairRepr n).symm
        (sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n (x + z))) =
      (sourcePairRepr n).symm
        (sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x)) +
      (sourcePairRepr n).symm
        (sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n z))
    rw [(sourcePairRepr n).map_add, map_add]
    exact sourcePairRepr_symm_map_add_actual n
      (sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x))
      (sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n z))
  map_smul' a x := by
    apply Subtype.ext
    change (sourcePairRepr n).symm
        (sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n (a • x))) =
      a • (sourcePairRepr n).symm
        (sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x))
    rw [(sourcePairRepr n).map_smul, map_smul]
    exact sourcePairRepr_symm_map_smul_actual n a
      (sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x))

/-- The positive resolvent is a right inverse of the source free shift. -/
theorem recoveredActualSourceFullImaginaryResolvent_right_inverse
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SourcePairL2) :
    recoveredActualSourceFreeShiftedDirac n (Complex.I * (y : ℂ))
      (recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE n y hy x) = x := by
  apply (sourcePairRepr n).toLinearEquiv.injective
  change sourcePairRepr n
      (recoveredActualSourceFreeShiftedDirac n (Complex.I * (y : ℂ))
        (recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE n y hy x)) =
    sourcePairRepr n x
  have hcoord :
      (⟨sourcePairRepr n
          (recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE n y hy x),
        (recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE n y hy x).property⟩ :
          freeWeightedDomainPointwise n) =
        ⟨sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x),
          sourceFullImaginaryResolventSquare_mem_freeWeightedDomain n y hy
            (sourcePairRepr n x)⟩ := by
    apply Subtype.ext
    dsimp [recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE,
      recoveredActualSourceFullImaginaryResolventDomain]
    change (sourcePairRepr n).toLinearEquiv
        ((sourcePairRepr n).toLinearEquiv.symm
          (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x))) = _
    exact sourcePairRepr_toLinearEquiv_apply_symm n _
  rw [recoveredActualSourceFreeShiftedDirac_repr_apply, hcoord]
  exact sourceFullImaginaryResolventSquare_right_inverse n y hy (sourcePairRepr n x)

/-- The negative resolvent is a right inverse of the source free shift. -/
theorem recoveredActualSourceFullNegativeImaginaryResolvent_right_inverse
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SourcePairL2) :
    recoveredActualSourceFreeShiftedDirac n (-Complex.I * (y : ℂ))
      (recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy x) = x := by
  apply (sourcePairRepr n).toLinearEquiv.injective
  change sourcePairRepr n
      (recoveredActualSourceFreeShiftedDirac n (-Complex.I * (y : ℂ))
        (recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy x)) =
    sourcePairRepr n x
  have hcoord :
      (⟨sourcePairRepr n
          (recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy x),
        (recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy x).property⟩ :
          freeWeightedDomainPointwise n) =
        ⟨sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x),
          sourceFullNegativeImaginaryResolventSquare_mem_freeWeightedDomain n y hy
            (sourcePairRepr n x)⟩ := by
    apply Subtype.ext
    dsimp [recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE]
    change (sourcePairRepr n).toLinearEquiv
        ((sourcePairRepr n).toLinearEquiv.symm
          (sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x))) = _
    exact sourcePairRepr_toLinearEquiv_apply_symm n _
  rw [recoveredActualSourceFreeShiftedDirac_repr_apply, hcoord]
  exact sourceFullNegativeImaginaryResolventSquare_right_inverse n y hy
    (sourcePairRepr n x)

/-- The potential acts on the recovered weighted source domain by transporting
to its actual Fourier representative and applying the accepted physical
source-pair potential map. -/
def actualSourcePotentialOnRecoveredWeightedDomainAfterAE
    (n : ℤ) (u₁ u₂ : PhysicalL2) :
    recoveredActualSourceFreeWeightedDomain n →ₗ[ℂ] SourcePairL2 :=
  (actualSourcePotentialOnWeightedDomain n u₁ u₂).comp
    (recoveredActualSourceWeightedDomainSequenceMapAfterAE n)

/-- The potential of the positive resolvent state is the actual positive
source `V R₀` map. -/
theorem actualSourcePotentialOnRecoveredWeightedDomain_fullPositiveResolvent
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2) (x : SourcePairL2) :
    actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂
      (recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE n y hy x) =
        actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂ x := by
  change actualSourcePotentialOnWeightedDomain n u₁ u₂
      (recoveredActualSourceWeightedDomainSequenceMapAfterAE n
        (recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE n y hy x)) = _
  have hvalue :
      recoveredActualSourceWeightedDomainSequenceMapAfterAE n
          (recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE n y hy x) =
        ⟨sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x),
          sourceFullImaginaryResolventSquare_mem_freeWeightedDomain n y hy
            (sourcePairRepr n x)⟩ := by
    apply Subtype.ext
    simp [recoveredActualSourceWeightedDomainSequenceMapAfterAE,
      recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE,
      recoveredActualSourceFullImaginaryResolventDomain]
  rw [hvalue]
  exact actualSourcePotentialOnWeightedDomain_fullResolvent n y hy u₁ u₂ x

/-- The potential of the negative resolvent state is the actual negative
source `V R₀` map. -/
theorem actualSourcePotentialOnRecoveredWeightedDomain_fullNegativeResolvent
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2) (x : SourcePairL2) :
    actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂
      (recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy x) =
        actualRoughL2PotentialFullNegativeImaginaryResolventCLM n y hy u₁ u₂ x := by
  change actualSourcePotentialOnWeightedDomain n u₁ u₂
      (recoveredActualSourceWeightedDomainSequenceMapAfterAE n
        (recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy x)) = _
  have hvalue :
      recoveredActualSourceWeightedDomainSequenceMapAfterAE n
          (recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy x) =
        ⟨sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x),
          sourceFullNegativeImaginaryResolventSquare_mem_freeWeightedDomain n y hy
            (sourcePairRepr n x)⟩ := by
    apply Subtype.ext
    simp [recoveredActualSourceWeightedDomainSequenceMapAfterAE,
      recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE]
  rw [hvalue]
  exact actualSourcePotentialOnWeightedDomain_fullNegativeResolvent n y hy u₁ u₂ x

/-- Actual source-space perturbed shift `z-D-V` on the recovered weighted
domain. -/
def actualSourcePerturbedShiftedDiracAfterAE
    (n : ℤ) (z : ℂ) (u₁ u₂ : PhysicalL2) :
    recoveredActualSourceFreeWeightedDomain n →ₗ[ℂ] SourcePairL2 :=
  recoveredActualSourceFreeShiftedDirac n z -
    actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂

/-- The positive-imaginary perturbed source shift is onto whenever the actual
source factor `1 - V R₀` has a right inverse. -/
theorem actualSourcePerturbedPositiveImaginaryShift_surjective_of_factor_right_inverse
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2)
    (S : SourcePairL2 →L[ℂ] SourcePairL2)
    (hS : ∀ x, (1 - actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂)
        (S x) = x) :
    Function.Surjective
      (actualSourcePerturbedShiftedDiracAfterAE n (Complex.I * (y : ℂ)) u₁ u₂) := by
  intro x
  refine ⟨recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE n y hy (S x), ?_⟩
  change recoveredActualSourceFreeShiftedDirac n (Complex.I * (y : ℂ))
        (recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE n y hy (S x)) -
      actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂
        (recoveredActualSourceFullImaginaryResolventDomainLinearMapAfterAE n y hy (S x)) = x
  rw [recoveredActualSourceFullImaginaryResolvent_right_inverse,
    actualSourcePotentialOnRecoveredWeightedDomain_fullPositiveResolvent]
  simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using hS x

/-- The negative-imaginary perturbed source shift is onto whenever the actual
source factor `1 - V R₀` has a right inverse. -/
theorem actualSourcePerturbedNegativeImaginaryShift_surjective_of_factor_right_inverse
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2)
    (S : SourcePairL2 →L[ℂ] SourcePairL2)
    (hS : ∀ x, (1 - actualRoughL2PotentialFullNegativeImaginaryResolventCLM n y hy u₁ u₂)
        (S x) = x) :
    Function.Surjective
      (actualSourcePerturbedShiftedDiracAfterAE n (-Complex.I * (y : ℂ)) u₁ u₂) := by
  intro x
  refine ⟨recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy (S x), ?_⟩
  change recoveredActualSourceFreeShiftedDirac n (-Complex.I * (y : ℂ))
        (recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy (S x)) -
      actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂
        (recoveredActualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy (S x)) = x
  rw [recoveredActualSourceFullNegativeImaginaryResolvent_right_inverse,
    actualSourcePotentialOnRecoveredWeightedDomain_fullNegativeResolvent]
  simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using hS x

end NlsGge.Schur

end
