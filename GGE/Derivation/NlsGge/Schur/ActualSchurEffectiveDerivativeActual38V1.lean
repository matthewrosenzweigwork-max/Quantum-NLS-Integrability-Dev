import NlsGge.Batch37.ActualSchurSandwichResolventDerivative37MinimumV3
import NlsGge.Schur.ActualSchurEffectiveDerivativeSupportV1_32
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot
namespace NlsGge.Schur
set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual high-frequency Schur effective operator has source-ordered
spectral derivative minus the checked Green row-column product. The actual
resolvent derivative is realized by checkpoint36, not assumed as a hypothesis.
This reassembles the preserved checkpoint32 target through a separate checked
sandwich derivative minimum; moving-center and Cauchy obligations remain open. -/
theorem actualSchurEffective_hasFDerivAt_actualResolvent38V1
    (radius : ℝ) (hradius : 1 ≤ radius)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * radius ^ 2 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hp₁ : ‖p.1‖ ≤ radius) (hp₂ : ‖p.2‖ ≤ radius) :
    HasFDerivAt (actualSchurEffectiveSpectralLineV3_32 n p)
      (ContinuousLinearMap.toSpanSingleton ℂ
        (-(actualSchurGreenDerivativeProductV3_31 n z p hz))) z := by
  let E : Type := ParityPair n →L[ℂ] ParityPair n
  let nr : NormedRing E := ContinuousLinearMap.toNormedRing
  letI : NormedRing E := nr
  let un : NonUnitalNormedRing E := nr.toNonUnitalNormedRing
  letI : NonUnitalNormedRing E := un
  letI : NormedAddCommGroup E := un.toNormedAddCommGroup
  let na : NormedAlgebra ℂ E := ContinuousLinearMap.toNormedAlgebra
  letI : NormedAlgebra ℂ E := na
  let alg : Algebra ℂ E := na.toAlgebra
  letI : Algebra ℂ E := alg
  let ns : NormedSpace ℂ E := NormedAlgebra.toNormedSpace E
  letI : NormedSpace ℂ E := ns
  letI : Module ℂ E := ns.toModule
  letI : DistribMulAction ℂ E := ns.toModule.toDistribMulAction
  letI : DistribSMul ℂ E := DistribMulAction.toDistribSMul
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  let V : ParityPair n →L[ℂ] ParityPair n :=
    actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p
  let R : ℂ → E :=
    actualSchurResolventFamilyAfterDextV3_32 n p
  let L : E →L[ℂ] E :=
    actualSchurGreenSandwichMapV3_32 n p
  let C : ParityPair n →L[ℂ] ParityPair n := P.comp (V.comp P)

  have hLformula (T : E) : L T =
      P.comp (V.comp (T.comp (V.comp P))) := by
    dsimp [L, actualSchurGreenSandwichMapV3_32]
    exact actualSchurGreenSandwichCLMMinimumV3_32_apply n p T

  have hRraw : R z =
      (freeResolventParityPair n z hz).comp
        (actualComplementaryQVDJointInverseV5_30 n (z, p)) := by
    dsimp [R, actualSchurResolventFamilyAfterDextV3_32]
    rw [actualFreeResolventCenterExtension_eq_actualV1_30 n z hz]

  have hrow : actualSchurGreenRowV5_31 n z p hz =
      P.comp (V.comp (R z)) := by
    let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
    let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
    let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
    let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
    have hV : actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p =
        coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n := by
      dsimp [u₁, u₂, hu₁, hu₂]
      exact actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n p
    change P.comp ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp
        ((freeResolventParityPair n z hz).comp
          (actualComplementaryQVDJointInverseV5_30 n (z, p)))) = _
    rw [← hV, ← hRraw]

  have hcolumn : actualSchurGreenColumnV5_31 n z p hz =
      (R z).comp (V.comp P) := by
    let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
    let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
    let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
    let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
    have hV : actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p =
        coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n := by
      dsimp [u₁, u₂, hu₁, hu₂]
      exact actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n p
    change ((freeResolventParityPair n z hz).comp
        (actualComplementaryQVDJointInverseV5_30 n (z, p))).comp
          ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp P) = _
    rw [← hRraw, ← hV]

  have hproduct : actualSchurGreenDerivativeProductV3_31 n z p hz =
      L ((R z).comp (R z)) := by
    rw [actualSchurGreenDerivativeProductV3_31, hrow, hcolumn]
    rw [hLformula]
    ext x
    rfl

  have hcomposed := actualSchurSandwichResolvent_hasFDerivAt37MinimumV3
    radius hradius n hn hlarge p z hz hp₁ hp₂
  change HasFDerivAt (fun w : ℂ => L (R w))
    (ContinuousLinearMap.toSpanSingleton ℂ (-(L ((R z).comp (R z))))) z at hcomposed
  rw [← hproduct] at hcomposed
  have hline : HasFDerivAt (fun w : ℂ => C + L (R w))
      (ContinuousLinearMap.toSpanSingleton ℂ
        (-(actualSchurGreenDerivativeProductV3_31 n z p hz))) z :=
    hcomposed.const_add C

  have hrepresentation : actualSchurEffectiveSpectralLineV3_32 n p =
      fun w : ℂ => C + L (R w) := by
    funext w
    dsimp [actualSchurEffectiveSpectralLineV3_32,
      actualSchurEffectiveOperatorAfterDextV3_30,
      actualSchurResolventFamilyAfterDextV3_32,
      C, R, P, V,
      actualComplementaryQVDJointInverseV5_30,
      actualComplementaryQVDJointParameterV5_30]
    rw [hLformula]

  rw [hrepresentation]
  exact hline

end NlsGge.Schur
end
