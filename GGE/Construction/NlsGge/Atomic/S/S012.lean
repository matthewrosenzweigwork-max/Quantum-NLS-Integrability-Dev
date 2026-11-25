import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualComplementaryQVDJointInverseAnalyticAfterDextV5_30
import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30
import NlsGge.Schur.ActualSchurEffectiveDerivativeSupportV1_32

                                                                                                           
                                                                                                                     
                                                                                                               
                                                                                                              
                                                                                                                    
                                            
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

/-- Generic: the composition `(f y).comp (g y)`, written as `compL`, is analytic at `x` when the two factors
are analytic at `x` (bilinear composition, then `AnalyticAt.comp₂`). -/
theorem s012_compL_analyticAt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : X → F →L[𝕜] G} {g : X → E →L[𝕜] F} {x : X}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
    AnalyticAt 𝕜 (fun y => ContinuousLinearMap.compL 𝕜 E F G (f y) (g y)) x :=
  AnalyticAt.comp₂
    (h := fun q : (F →L[𝕜] G) × (E →L[𝕜] F) => ContinuousLinearMap.compL 𝕜 E F G q.1 q.2)
    (f := f) (g := g)
    ((ContinuousLinearMap.compL 𝕜 E F G).analyticAt_bilinear (f x, g x)) hf hg

private theorem s012_center_analytic (n : ℤ) (z : ℂ)
    (hball : z ∈ Metric.ball (spectralCenter n) 2) :
    AnalyticAt ℂ (actualFreeResolventCenterExtensionV1_30 n) z :=
  actualFreeResolventCenterExtension_analyticOnNhdV1_30 n z hball

private theorem s012_joint_inverse_analytic (R : ℝ) (hR : 1 ≤ R) (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant * R ^ 2 ≤
      |(n : ℝ)|)
    (z : ℂ) (p : SchurPair) (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    AnalyticAt ℂ (fun x : ℂ × SchurPair => actualComplementaryQVDJointInverseV5_30 n x) (z, p) := by
  have h := analyticOnNhd_actualComplementaryQVDJointInverseAfterDextV5_30 R hR n hn hlarge
    (z, p) ⟨hz, hp₁, hp₂⟩
  simpa only [actualComplementaryQVDJointInverseV5_30] using h

private theorem s012_bilinear_comp_analytic (n : ℤ) (z : ℂ) (p : SchurPair)
    (hD : AnalyticAt ℂ (actualFreeResolventCenterExtensionV1_30 n) z)
    (hJ : AnalyticAt ℂ (fun x : ℂ × SchurPair => actualComplementaryQVDJointInverseV5_30 n x) (z, p)) :
    AnalyticAt ℂ (fun x : ℂ × SchurPair =>
      ContinuousLinearMap.compL ℂ (ParityPair n) (ParityPair n) (ParityPair n)
        (actualFreeResolventCenterExtensionV1_30 n x.1) (actualComplementaryQVDJointInverseV5_30 n x))
      (z, p) := by
  have hfst : AnalyticAt ℂ (fun x : ℂ × SchurPair => x.1) (z, p) := analyticAt_fst
  have hDp : AnalyticAt ℂ (fun x : ℂ × SchurPair => actualFreeResolventCenterExtensionV1_30 n x.1)
      (z, p) :=
    AnalyticAt.comp (f := fun x : ℂ × SchurPair => x.1) (g := actualFreeResolventCenterExtensionV1_30 n)
      hD hfst
  exact s012_compL_analyticAt (𝕜 := ℂ) (E := ParityPair n) (F := ParityPair n) (G := ParityPair n)
    (f := fun x : ℂ × SchurPair => actualFreeResolventCenterExtensionV1_30 n x.1)
    (g := fun x : ℂ × SchurPair => actualComplementaryQVDJointInverseV5_30 n x)
    (x := (z, p)) hDp hJ

private theorem s012_resolvent_analytic_at (R : ℝ) (hR : 1 ≤ R) (n : ℤ) (z : ℂ) (p : SchurPair)
    (hball : z ∈ Metric.ball (spectralCenter n) 2)
    (hlarge : 4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant * R ^ 2 ≤
      |(n : ℝ)|)
    (hn : 1 ≤ |(n : ℝ)|) (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    AnalyticAt ℂ (fun x : ℂ × SchurPair => resolventFamily n x.1 x.2) (z, p) := by
  have hD := s012_center_analytic n z hball
  have hJ := s012_joint_inverse_analytic R hR n hn hlarge z p hz hp₁ hp₂
  have hcompL := s012_bilinear_comp_analytic n z p hD hJ
  simp only [resolventFamily, actualSchurResolventFamilyAfterDextV3_32, Prod.mk.eta,
    ← ContinuousLinearMap.compL_apply]
  exact hcompL

theorem complementaryResolvent_analyticAt :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (n : ℤ) (z : ℂ) (p : SchurPair),
      schurParameterDomain K R n z p →
      AnalyticAt ℂ (fun x : ℂ × SchurPair => resolventFamily n x.1 x.2) (z, p) := by
  refine ⟨|4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant| + 1, by positivity, ?_⟩
  intro R n z p hdom
  unfold schurParameterDomain at hdom
  obtain ⟨hR, hn0, hK, hz, hp₁, hp₂⟩ := hdom
  have hn : 1 ≤ |(n : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast h1
  have hlarge : 4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant * R ^ 2 ≤
      |(n : ℝ)| := by
    have hle := le_abs_self (4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant)
    have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
    have h2 : 4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant * R ^ 2 ≤
        (|4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant| + 1) * R ^ 2 := by
      rw [add_mul, one_mul]
      exact le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_right hle hR2) hR2
    exact le_trans h2 hK
  have hz1 : ‖z - spectralCenter n‖ ≤ 1 := hz
  have hball : z ∈ Metric.ball (spectralCenter n) 2 := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt hz1 (by norm_num)
  exact s012_resolvent_analytic_at R hR n z p hball hlarge hn hz hp₁ hp₂

end NlsGge.ThirdConsultation.S
