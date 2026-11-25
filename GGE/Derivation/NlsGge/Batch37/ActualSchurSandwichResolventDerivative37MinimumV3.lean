import NlsGge.Schur.RootActualSchurResolventAfterDextHasFDerivAtNegativeSquareMinimum36V8
import NlsGge.Schur.ActualSchurEffectiveDerivativeSupportV1_32
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
set_option autoImplicit false
noncomputable section
namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot
set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Concrete fixed-potential sandwich of the actual complementary resolvent
has its spectral derivative obtained by the checked actual R'=-R² theorem.
This isolates the CLM/complex-span chain rule prerequisite behind the three
preserved failed whole effective-derivative attempts in checkpoint32. -/
theorem actualSchurSandwichResolvent_hasFDerivAt37MinimumV3
    (radius : ℝ) (hradius : 1 ≤ radius)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * radius ^ 2 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hp₁ : ‖p.1‖ ≤ radius) (hp₂ : ‖p.2‖ ≤ radius) :
    HasFDerivAt
      (fun w : ℂ => actualSchurGreenSandwichMapV3_32 n p
        (actualSchurResolventFamilyAfterDextV3_32 n p w))
      (ContinuousLinearMap.toSpanSingleton ℂ
        (-(actualSchurGreenSandwichMapV3_32 n p
          ((actualSchurResolventFamilyAfterDextV3_32 n p z).comp
            (actualSchurResolventFamilyAfterDextV3_32 n p z))))) z := by
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
  let L := actualSchurGreenSandwichMapV3_32 n p
  let R := actualSchurResolventFamilyAfterDextV3_32 n p
  have hR := rootActualSchurResolventFamilyAfterDext_hasFDerivAt_negativeSquareMinimum36V8
    radius hradius n hn hlarge p z hz hp₁ hp₂
  have hlinear : HasFDerivAt (fun X : E => L X) L (R z) := L.hasFDerivAt
  have h := hlinear.comp z hR
  have hmap :
      L.comp (ContinuousLinearMap.toSpanSingleton ℂ (-((R z).comp (R z)))) =
        ContinuousLinearMap.toSpanSingleton ℂ (-(L ((R z).comp (R z)))) := by
    apply ContinuousLinearMap.ext
    intro δ
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.map_smul, ContinuousLinearMap.map_neg]
  exact h.congr_fderiv hmap
end NlsGge.Schur
end
