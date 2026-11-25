import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurAlphaBoundAfterDextV6_32

                                                                                                           
                                                                                                                     
                                                                                                          
                                                                                   
                                                                                                                   
                                                                                                                
                                                                                                      
                                                                                                                   
                                                                                                                    
                                                   
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem schur_alpha_bound :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (R : ℝ) (n : ℤ) (z : ℂ) (p : SchurPair),
        schurParameterDomain K R n z p →
        ‖alphaAt n z p‖ ≤ C * R ^ 3 / |(n : ℝ)| := by
  refine ⟨|2 * freeResolventSchurUniformConstant * freeResolventComplementaryInverseUniformConstant22 *
      physicalH1MultiplierConstant| + 1,
    |4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant| + 1, by positivity, by positivity, ?_⟩
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
  have hbound := actualSchurAlpha_boundAfterDextV6_32 R hR n hn hlarge z p hz hp₁ hp₂
  have hC : 2 * freeResolventSchurUniformConstant * freeResolventComplementaryInverseUniformConstant22 *
      physicalH1MultiplierConstant ≤
      |2 * freeResolventSchurUniformConstant * freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant| + 1 := by
    have := le_abs_self (2 * freeResolventSchurUniformConstant *
      freeResolventComplementaryInverseUniformConstant22 * physicalH1MultiplierConstant)
    linarith
  have hR3 : 0 ≤ R ^ 3 := pow_nonneg (by linarith) 3
  calc ‖alphaAt n z p‖
      = ‖actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (true, resonantIndex n) (z, p)‖ := rfl
    _ ≤ 2 * freeResolventSchurUniformConstant * freeResolventComplementaryInverseUniformConstant22 *
          physicalH1MultiplierConstant * R ^ 3 / |(n : ℝ)| := hbound
    _ ≤ (|2 * freeResolventSchurUniformConstant * freeResolventComplementaryInverseUniformConstant22 *
          physicalH1MultiplierConstant| + 1) * R ^ 3 / |(n : ℝ)| :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hR3) (abs_nonneg _)

end NlsGge.ThirdConsultation.S
