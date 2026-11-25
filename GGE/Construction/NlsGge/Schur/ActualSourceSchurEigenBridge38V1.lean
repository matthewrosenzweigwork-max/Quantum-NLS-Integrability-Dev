import NlsGge.Spectral.ActualSourcePerturbedDiracFormalSymmetryPhysicalSliceV6
import NlsGge.Schur.ActualSourcePotentialSchurCoherence38V1
import NlsGge.Schur.ActualSchurElimination38V1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis
open TransportBridgeV4

/-- The source potential, read in Fourier coordinates, is the transported
covered-`H¹` parity-pair potential `repr ∘ V ∘ repr.symm`. -/
theorem sourcePairRepr_actualSourcePotentialOnRecovered_eq
    (n : ℤ) (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (Y : recoveredActualSourceFreeWeightedDomain n) :
    sourcePairRepr n (actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ Y) =
      actualSchurEndomorphismToSquareV5_30 n
        (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n)
        (recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y).val := by
  have hB := actualSourcePotentialOnWeightedDomain_eq_coveredH1ParityPairPotential
    n u₁ u₂ hu₁ hu₂ (recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y)
  change sourcePairRepr n
      (actualSourcePotentialOnWeightedDomain n u₁ u₂
        (recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y)) = _
  rw [hB]
  change (parityPairRepr n) ((parityPairIntervalEquiv n).symm
    (parityPairIntervalEquiv n _)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- Source eigenvalue problem for the actual perturbed Dirac operator (on the
H¹ potential slice) is equivalent to the Fourier-coordinate kernel problem
`(z - L₀ - Ṽ) x = 0`, `Ṽ = repr ∘ V ∘ repr.symm`. -/
theorem actualSourcePerturbedDirac_eigenvalue_iff_coordinate_kernel38V1
    (n : ℤ) (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) (z : ℂ) :
    (∃ Y : recoveredActualSourceFreeWeightedDomain n, Y.val ≠ 0 ∧
        actualSourcePerturbedDiracPMapAfterAE n u₁ u₂ Y = z • Y.val) ↔
      (∃ x : freeWeightedDomainPointwise n, x.val ≠ 0 ∧
        z • x.val - freeCoordinateDirac n x -
          actualSchurEndomorphismToSquareV5_30 n
            (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n) x.val = 0) := by
  -- key equivalence for a single vector
  have key : ∀ Y : recoveredActualSourceFreeWeightedDomain n,
      actualSourcePerturbedDiracPMapAfterAE n u₁ u₂ Y = z • Y.val ↔
        z • (recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y).val -
          freeCoordinateDirac n (recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y) -
          actualSchurEndomorphismToSquareV5_30 n
            (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n)
            (recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y).val = 0 := by
    intro Y
    have hact : actualSourcePerturbedDiracPMapAfterAE n u₁ u₂ Y =
        actualSourceFreeDiracMapAfterAE n Y +
          actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ Y := rfl
    have hrepr : sourcePairRepr n (actualSourcePerturbedDiracPMapAfterAE n u₁ u₂ Y) =
        freeCoordinateDirac n (recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y) +
          actualSchurEndomorphismToSquareV5_30 n
            (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n)
            (recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y).val := by
      rw [hact, map_add, actualSourceFreeDiracMapAfterAE_repr_apply,
        sourcePairRepr_actualSourcePotentialOnRecovered_eq n u₁ u₂ hu₁ hu₂ Y]
    have hz : sourcePairRepr n (z • Y.val) =
        z • (recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y).val := by
      rw [map_smul]; rfl
    constructor
    · intro h
      have h2 := congrArg (sourcePairRepr n) h
      rw [hrepr, hz] at h2
      rw [← h2]; abel
    · intro h
      apply (sourcePairRepr n).injective
      rw [hrepr, hz]
      rw [sub_sub, sub_eq_zero] at h
      exact h.symm
  constructor
  · rintro ⟨Y, hY0, hY⟩
    refine ⟨recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y, ?_, (key Y).mp hY⟩
    intro h0
    apply hY0
    have : sourcePairRepr n Y.val = 0 := h0
    exact (map_eq_zero_iff _ (sourcePairRepr n).injective).mp this
  · rintro ⟨x, hx0, hx⟩
    let Y : recoveredActualSourceFreeWeightedDomain n :=
      ⟨(sourcePairRepr n).symm x.val, by
        change sourcePairRepr n ((sourcePairRepr n).symm x.val) ∈ freeWeightedDomainPointwise n
        rw [LinearIsometryEquiv.apply_symm_apply]; exact x.property⟩
    have hYx : (recoveredActualSourceWeightedDomainSequenceMapAfterAE n Y) = x :=
      Subtype.ext (LinearIsometryEquiv.apply_symm_apply _ _)
    refine ⟨Y, ?_, (key Y).mpr (by rw [hYx]; exact hx)⟩
    intro h0
    apply hx0
    have : Y.val = 0 := h0
    have h1 : x.val = sourcePairRepr n Y.val := (LinearIsometryEquiv.apply_symm_apply _ _).symm
    rw [h1, this, map_zero]

/-- For the carrier pair `p`, the transported covered-`H¹` potential of the
carrier images is T3's `actualSchurCoordinatePotential38 n p`. -/
theorem actualSchurCoordinatePotential38_eq_covered
    (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) :
    actualSchurCoordinatePotential38 n p =
      actualSchurEndomorphismToSquareV5_30 n
        (coveredH1ParityPairPotential
          (physicalH1ComplexCarrierToL2Actual22 p.1)
          (physicalH1ComplexCarrierToL2Actual22 p.2)
          (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)
          (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2) n) := by
  unfold actualSchurCoordinatePotential38
  rw [actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply]

/-- Source eigenvalue problem (carrier images as potentials) is equivalent to
T3's coordinate kernel problem. -/
theorem actualSourcePerturbedDirac_eigenvalue_iff_schurCoordinate38V1
    (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) (z : ℂ) :
    (∃ Y : recoveredActualSourceFreeWeightedDomain n, Y.val ≠ 0 ∧
        actualSourcePerturbedDiracPMapAfterAE n
          (physicalH1ComplexCarrierToL2Actual22 p.1)
          (physicalH1ComplexCarrierToL2Actual22 p.2) Y = z • Y.val) ↔
      (∃ x : freeWeightedDomainPointwise n, x.val ≠ 0 ∧
        z • x.val - freeCoordinateDirac n x -
          actualSchurCoordinatePotential38 n p x.val = 0) := by
  rw [actualSourcePerturbedDirac_eigenvalue_iff_coordinate_kernel38V1 n _ _
    (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)
    (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2) z,
    actualSchurCoordinatePotential38_eq_covered]

/-- Source eigenvalue of the actual perturbed Dirac operator iff the actual
secular determinant vanishes, under the source threshold. -/
theorem actualSourcePerturbedDirac_eigenvalue_iff_secularDet_zero_threshold38V1
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualSchurEffectiveH1PairV3_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    (∃ Y : recoveredActualSourceFreeWeightedDomain n, Y.val ≠ 0 ∧
        actualSourcePerturbedDiracPMapAfterAE n
          (physicalH1ComplexCarrierToL2Actual22 p.1)
          (physicalH1ComplexCarrierToL2Actual22 p.2) Y = z • Y.val) ↔
      actualSchurSecularDet38 n z p = 0 := by
  rw [actualSourcePerturbedDirac_eigenvalue_iff_schurCoordinate38V1]
  exact actualSchur_eigenvalue_iff_secularDet_zero_threshold38V1 R hR n hthr z p hz hp₁ hp₂

end NlsGge.Schur

end
