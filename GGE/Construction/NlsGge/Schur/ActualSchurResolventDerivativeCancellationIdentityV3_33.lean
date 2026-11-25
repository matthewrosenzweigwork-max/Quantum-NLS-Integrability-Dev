import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30
import NlsGge.Schur.ActualComplementaryQVDJointInverseAndEqualDiagonalV5_30
import NlsGge.Schur.ActualSchurEffectiveJointAnalyticAfterDextV3_30
import NlsGge.Schur.ActualSchurParityPairCLMCompositionIdentityMinimumV1_33

set_option autoImplicit false
noncomputable section
open scoped Topology RightActions

namespace NlsGge.Schur

/-- The exact actual inverse-cancellation identity behind differentiating the
source-order complementary resolvent `D S`. It is independent of a derivative
claim: the only input is the checked actual left-inverse equation for
`S = (1 - Q V D)⁻¹` on the original signed spectral disk and independent H¹
balls. -/
theorem actualSchurResolventDerivativeCancellationIdentityV3_33
    (radius : ℝ) (hradius : 1 ≤ radius)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      NlsGge.Analysis.physicalH1MultiplierConstant * radius ^ 2 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hp₁ : ‖p.1‖ ≤ radius) (hp₂ : ‖p.2‖ ≤ radius) :
    let D : ParityPair n →L[ℂ] ParityPair n :=
      actualFreeResolventCenterExtensionV1_30 n z
    let T : ParityPair n →L[ℂ] ParityPair n :=
      actualComplementaryQVDJointParameterV5_30 n (z, p)
    let S : ParityPair n →L[ℂ] ParityPair n :=
      actualComplementaryQVDJointInverseV5_30 n (z, p)
    (D.comp D).comp S +
        (D.comp S).comp (T.comp (D.comp S)) =
      (D.comp S).comp (D.comp S) := by
  let D : ParityPair n →L[ℂ] ParityPair n :=
    actualFreeResolventCenterExtensionV1_30 n z
  let T : ParityPair n →L[ℂ] ParityPair n :=
    actualComplementaryQVDJointParameterV5_30 n (z, p)
  let S : ParityPair n →L[ℂ] ParityPair n :=
    actualComplementaryQVDJointInverseV5_30 n (z, p)

  have hSleft : S.comp (1 - T) = 1 := by
    exact (actualComplementaryQVDJointInverseV5_30_twoSided
      radius hradius n hn hlarge z p hz hp₁ hp₂).1
  have hSrelation : S = 1 + S.comp T := by
    calc
      S = S.comp 1 := by
        exact (actualSchurParityPairCLMCompositionIdentityMinimumV1_33 n S).1.symm
      _ = S.comp ((1 - T) + T) := by
        exact congrArg (fun X : ParityPair n →L[ℂ] ParityPair n => S.comp X)
          (sub_add_cancel 1 T).symm
      _ = S.comp (1 - T) + S.comp T :=
        ContinuousLinearMap.comp_add _ _ _
      _ = 1 + S.comp T := by rw [hSleft]
  have haux :
      (D.comp S) + S.comp (T.comp (D.comp S)) =
        S.comp (D.comp S) := by
    calc
      (D.comp S) + S.comp (T.comp (D.comp S)) =
          (1 + S.comp T).comp (D.comp S) := by
            rw [ContinuousLinearMap.add_comp,
              (actualSchurParityPairCLMCompositionIdentityMinimumV1_33 n
                (D.comp S)).2,
              ContinuousLinearMap.comp_assoc]
      _ = S.comp (D.comp S) := by rw [← hSrelation]
  calc
    (D.comp D).comp S +
        (D.comp S).comp (T.comp (D.comp S)) =
      D.comp ((D.comp S) + S.comp (T.comp (D.comp S))) := by
        simp only [ContinuousLinearMap.comp_assoc,
          ContinuousLinearMap.comp_add]
    _ = D.comp (S.comp (D.comp S)) := by rw [haux]
    _ = (D.comp S).comp (D.comp S) := by
      simp only [ContinuousLinearMap.comp_assoc]

end NlsGge.Schur
