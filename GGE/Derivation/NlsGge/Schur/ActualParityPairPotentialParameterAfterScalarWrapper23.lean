import NlsGge.Schur.ActualParityScalarMultiplierExplicitCLMWrapper23
import NlsGge.Schur.CoveredH1ParityPairPotentialNorm
import NlsGge.Schur.PhysicalSector
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

local notation "H1PairAfterScalar23" =>
  WeightedHilbert (sobolevModeWeight (1 : ℝ)) ×
    WeightedHilbert (sobolevModeWeight (1 : ℝ))

/-- The actual physical weighted Fourier map preserves the H¹ norm. -/
theorem actualPhysicalH1Carrier_sobolev_normAfterScalar23
    (x : WeightedHilbert (sobolevModeWeight (1 : ℝ))) :
    ‖physicalSobolevL2 1 (physicalH1ComplexCarrierToL2Actual22 x)
      (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x)‖ = ‖x‖ := by
  have hrepr :
      physicalSobolevL2 1 (physicalH1ComplexCarrierToL2Actual22 x)
          (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x) =
        weightedLinearMap (sobolevModeWeight (1 : ℝ)) x := by
    apply lp.ext
    funext n
    change weightedCoordinates (sobolevModeWeight (1 : ℝ))
        (physicalFourier (physicalH1ComplexCarrierToL2Actual22 x)) n =
      weightedCoordinates (sobolevModeWeight (1 : ℝ)) (x : ℤ → ℂ) n
    simpa only [weightedCoordinates] using
      congrArg (fun z : ℂ =>
        (Real.sqrt (sobolevModeWeight (1 : ℝ) n) : ℂ) * z)
        (physicalH1ComplexCarrierToL2Actual22_fourier x n)
  rw [hrepr]
  exact (weightedIsometry (sobolevModeWeight (1 : ℝ))).norm_map x

private def actualParityPairPotentialOperatorAfterScalar23
    (n : ℤ) (p : H1PairAfterScalar23) : ParityPair n →L[ℂ] ParityPair n := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Bool => scalarParity n)
  let f : (Bool → scalarParity n) →L[ℂ] (Bool → scalarParity n) :=
    ContinuousLinearMap.pi (fun b : Bool =>
      if b then
        (actualParityScalarMultiplierParameterExplicitCLM23 n p.1).comp
          (ContinuousLinearMap.proj false)
      else
        (actualParityScalarMultiplierParameterExplicitCLM23 n p.2).comp
          (ContinuousLinearMap.proj true))
  exact e.symm.toContinuousLinearMap.comp (f.comp e.toContinuousLinearMap)

private theorem actualParityPairPotentialOperatorAfterScalar23_apply_true
    (n : ℤ) (p : H1PairAfterScalar23) (x : ParityPair n) :
    actualParityPairPotentialOperatorAfterScalar23 n p x true =
      actualParityScalarMultiplierParameterExplicitCLM23 n p.1 (x false) := by
  simp [actualParityPairPotentialOperatorAfterScalar23]

private theorem actualParityPairPotentialOperatorAfterScalar23_apply_false
    (n : ℤ) (p : H1PairAfterScalar23) (x : ParityPair n) :
    actualParityPairPotentialOperatorAfterScalar23 n p x false =
      actualParityScalarMultiplierParameterExplicitCLM23 n p.2 (x true) := by
  simp [actualParityPairPotentialOperatorAfterScalar23]

private theorem actualParityPairPotentialOperatorAfterScalar23_eq
    (n : ℤ) (p : H1PairAfterScalar23) :
    actualParityPairPotentialOperatorAfterScalar23 n p =
      coveredH1ParityPairPotential
        (physicalH1ComplexCarrierToL2Actual22 p.1)
        (physicalH1ComplexCarrierToL2Actual22 p.2)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2) n := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro b
  cases b
  · calc
      actualParityPairPotentialOperatorAfterScalar23 n p x false =
          actualParityScalarMultiplierParameterExplicitCLM23 n p.2 (x true) :=
        actualParityPairPotentialOperatorAfterScalar23_apply_false n p x
      _ = coveredH1ScalarParityMultiplier
          (physicalH1ComplexCarrierToL2Actual22 p.2)
          (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2) n (x true) := by
        rw [actualParityScalarMultiplierParameterExplicitCLM23_apply]
      _ = coveredH1ParityPairPotential
          (physicalH1ComplexCarrierToL2Actual22 p.1)
          (physicalH1ComplexCarrierToL2Actual22 p.2)
          (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)
          (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2) n x false :=
        (coveredH1ParityPairPotential_apply_false _ _ _ _ _ _).symm
  · calc
      actualParityPairPotentialOperatorAfterScalar23 n p x true =
          actualParityScalarMultiplierParameterExplicitCLM23 n p.1 (x false) :=
        actualParityPairPotentialOperatorAfterScalar23_apply_true n p x
      _ = coveredH1ScalarParityMultiplier
          (physicalH1ComplexCarrierToL2Actual22 p.1)
          (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1) n (x false) := by
        rw [actualParityScalarMultiplierParameterExplicitCLM23_apply]
      _ = coveredH1ParityPairPotential
          (physicalH1ComplexCarrierToL2Actual22 p.1)
          (physicalH1ComplexCarrierToL2Actual22 p.2)
          (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)
          (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2) n x true :=
        (coveredH1ParityPairPotential_apply_true _ _ _ _ _ _).symm

private def actualParityPairPotentialLinearAfterScalar23 (n : ℤ) :
    H1PairAfterScalar23 →ₗ[ℂ] (ParityPair n →L[ℂ] ParityPair n) where
  toFun := actualParityPairPotentialOperatorAfterScalar23 n
  map_add' p q := by
    apply ContinuousLinearMap.ext
    intro x
    apply PiLp.ext
    intro b
    cases b
    · calc
        actualParityPairPotentialOperatorAfterScalar23 n (p + q) x false =
            actualParityScalarMultiplierParameterExplicitCLM23 n (p.2 + q.2) (x true) := by
          rw [actualParityPairPotentialOperatorAfterScalar23_apply_false, Prod.snd_add]
        _ = actualParityScalarMultiplierParameterExplicitCLM23 n p.2 (x true) +
            actualParityScalarMultiplierParameterExplicitCLM23 n q.2 (x true) := by
          rw [(actualParityScalarMultiplierParameterExplicitCLM23 n).map_add,
            ContinuousLinearMap.add_apply]
        _ = (actualParityPairPotentialOperatorAfterScalar23 n p x +
            actualParityPairPotentialOperatorAfterScalar23 n q x) false := by
          rw [WithLp.ofLp_add, Pi.add_apply,
            actualParityPairPotentialOperatorAfterScalar23_apply_false,
            actualParityPairPotentialOperatorAfterScalar23_apply_false]
    · calc
        actualParityPairPotentialOperatorAfterScalar23 n (p + q) x true =
            actualParityScalarMultiplierParameterExplicitCLM23 n (p.1 + q.1) (x false) := by
          rw [actualParityPairPotentialOperatorAfterScalar23_apply_true, Prod.fst_add]
        _ = actualParityScalarMultiplierParameterExplicitCLM23 n p.1 (x false) +
            actualParityScalarMultiplierParameterExplicitCLM23 n q.1 (x false) := by
          rw [(actualParityScalarMultiplierParameterExplicitCLM23 n).map_add,
            ContinuousLinearMap.add_apply]
        _ = (actualParityPairPotentialOperatorAfterScalar23 n p x +
            actualParityPairPotentialOperatorAfterScalar23 n q x) true := by
          rw [WithLp.ofLp_add, Pi.add_apply,
            actualParityPairPotentialOperatorAfterScalar23_apply_true,
            actualParityPairPotentialOperatorAfterScalar23_apply_true]
  map_smul' c p := by
    apply ContinuousLinearMap.ext
    intro x
    apply PiLp.ext
    intro b
    cases b
    · calc
        actualParityPairPotentialOperatorAfterScalar23 n (c • p) x false =
            actualParityScalarMultiplierParameterExplicitCLM23 n (c • p.2) (x true) := by
          rw [actualParityPairPotentialOperatorAfterScalar23_apply_false]
          change actualParityScalarMultiplierParameterExplicitCLM23 n (c • p.2) (x true) = _
          rfl
        _ = c • actualParityScalarMultiplierParameterExplicitCLM23 n p.2 (x true) := by
          rw [(actualParityScalarMultiplierParameterExplicitCLM23 n).map_smul,
            ContinuousLinearMap.smul_apply]
        _ = (c • actualParityPairPotentialOperatorAfterScalar23 n p x) false := by
          rw [WithLp.ofLp_smul, Pi.smul_apply,
            actualParityPairPotentialOperatorAfterScalar23_apply_false]
    · calc
        actualParityPairPotentialOperatorAfterScalar23 n (c • p) x true =
            actualParityScalarMultiplierParameterExplicitCLM23 n (c • p.1) (x false) := by
          rw [actualParityPairPotentialOperatorAfterScalar23_apply_true]
          change actualParityScalarMultiplierParameterExplicitCLM23 n (c • p.1) (x false) = _
          rfl
        _ = c • actualParityScalarMultiplierParameterExplicitCLM23 n p.1 (x false) := by
          rw [(actualParityScalarMultiplierParameterExplicitCLM23 n).map_smul,
            ContinuousLinearMap.smul_apply]
        _ = (c • actualParityPairPotentialOperatorAfterScalar23 n p x) true := by
          rw [WithLp.ofLp_smul, Pi.smul_apply,
            actualParityPairPotentialOperatorAfterScalar23_apply_true]

/-- The actual paired potential depends continuously on the two independent
complex H¹ Fourier fields, with the inherited exact constant. -/
def actualParityPairPotentialParameterAfterScalarWrapperCLM23 (n : ℤ) :
    H1PairAfterScalar23 →L[ℂ] (ParityPair n →L[ℂ] ParityPair n) := by
  let f : H1PairAfterScalar23 →ₗ[ℂ] (ParityPair n →L[ℂ] ParityPair n) :=
    actualParityPairPotentialLinearAfterScalar23 n
  exact
    { toLinearMap := f
      cont := AddMonoidHomClass.continuous_of_bound f
        (2 * physicalH1MultiplierConstant) (by
          intro p
          change ‖actualParityPairPotentialOperatorAfterScalar23 n p‖ ≤
            2 * physicalH1MultiplierConstant * ‖p‖
          rw [actualParityPairPotentialOperatorAfterScalar23_eq]
          apply coveredH1ParityPairPotential_norm_bound
          · exact norm_nonneg p
          · rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
            exact norm_fst_le p
          · rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
            exact norm_snd_le p) }

theorem actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply
    (n : ℤ) (p : H1PairAfterScalar23) :
    actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p =
      coveredH1ParityPairPotential
        (physicalH1ComplexCarrierToL2Actual22 p.1)
        (physicalH1ComplexCarrierToL2Actual22 p.2)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2) n := by
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T x)
    (actualParityPairPotentialOperatorAfterScalar23_eq n p)

end NlsGge.Schur
