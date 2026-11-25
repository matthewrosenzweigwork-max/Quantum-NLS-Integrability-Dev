import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurFGboundAfterResolventFactorizationV5_31
import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30
import NlsGge.Schur.ActualParityPairPotentialParameterAfterScalarWrapper23

                                                                                                           
                                                                                                                     
                                                                                                                        
                                                                                                                 
                                                                                                     
                                                                                                    
                                                                                                      
                                                                                                                    
                                                                                                             
                                                                                                                      
                                                                    
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem schurLifts_bound :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (R : ℝ) (n : ℤ) (z : ℂ) (p : SchurPair),
        schurParameterDomain K R n z p →
        ‖greenColumn n z p‖ + ‖greenRow n z p‖ ≤ C * R ^ 2 / |(n : ℝ)| := by
  refine ⟨2 * |freeResolventComplementaryInverseUniformConstant22 * freeResolventSchurUniformConstant| + 1,
    |4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant| + 1, by positivity, by positivity,
    ?_⟩
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
      nlinarith
    linarith
  have hcol_eq : greenColumn n z p = actualSchurGreenColumnV5_31 n z p hz := by
    unfold greenColumn resolventFamily actualSchurResolventFamilyAfterDextV3_32 potentialAt
    rw [actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply,
      actualFreeResolventCenterExtension_eq_actualV1_30 n z hz]
    rfl
  have hrow_eq : greenRow n z p = actualSchurGreenRowV5_31 n z p hz := by
    unfold greenRow resolventFamily actualSchurResolventFamilyAfterDextV3_32 potentialAt
    rw [actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply,
      actualFreeResolventCenterExtension_eq_actualV1_30 n z hz]
    rfl
  have hcol := actualSchurGreenColumn_boundV5_31 R (by linarith) n hn hlarge z p hz hp₁ hp₂
  have hrow := actualSchurGreenRow_boundV5_31 R (by linarith) n hn hlarge z p hz hp₁ hp₂
  rw [hcol_eq, hrow_eq]
  have hq : 0 ≤ R ^ 2 / |(n : ℝ)| := by positivity
  have hc : 2 * (freeResolventComplementaryInverseUniformConstant22 * freeResolventSchurUniformConstant) ≤
      2 * |freeResolventComplementaryInverseUniformConstant22 * freeResolventSchurUniformConstant| + 1 := by
    have := le_abs_self (freeResolventComplementaryInverseUniformConstant22 * freeResolventSchurUniformConstant)
    linarith
  calc ‖actualSchurGreenColumnV5_31 n z p hz‖ + ‖actualSchurGreenRowV5_31 n z p hz‖
      ≤ freeResolventComplementaryInverseUniformConstant22 * freeResolventSchurUniformConstant * R ^ 2 /
          |(n : ℝ)| + freeResolventComplementaryInverseUniformConstant22 *
          freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)| := add_le_add hcol hrow
    _ = (2 * (freeResolventComplementaryInverseUniformConstant22 * freeResolventSchurUniformConstant)) *
          (R ^ 2 / |(n : ℝ)|) := by ring
    _ ≤ (2 * |freeResolventComplementaryInverseUniformConstant22 * freeResolventSchurUniformConstant| + 1) *
          (R ^ 2 / |(n : ℝ)|) := mul_le_mul_of_nonneg_right hc hq
    _ = (2 * |freeResolventComplementaryInverseUniformConstant22 * freeResolventSchurUniformConstant| + 1) *
          R ^ 2 / |(n : ℝ)| := by ring

end NlsGge.ThirdConsultation.S
