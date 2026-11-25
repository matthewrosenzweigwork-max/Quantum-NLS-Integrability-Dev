import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurOffDiagonalRemainder38V1
import NlsGge.Schur.PhysicalH1ComplexCarrierSchurBridge

                                                                                                           
                                                                                                                     
                                                                                             
                                                                            
                                                                                                            
                                                                                                                   
                                                                                                                        
                                                                                                                      
                                                                                              
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem schur_b_remainder_bound :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (R : ℝ) (n : ℤ) (z : ℂ) (p : SchurPair),
        schurParameterDomain K R n z p →
        ‖bAt n z p - p.1 n‖ ≤ C * R ^ 4 / |(n : ℝ)| ^ 2 ∧
        ‖cAt n z p - p.2 (-n)‖ ≤ C * R ^ 4 / |(n : ℝ)| ^ 2 := by
  refine ⟨|2 * freeResolventSchurUniformConstant ^ 2 *
        freeResolventComplementaryInverseUniformConstant22 * physicalH1MultiplierConstant| + 1,
      |4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant| + 1,
      by positivity, by positivity, ?_⟩
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
  have hb := actualSchurOffDiagonal_sub_fourier_bound38V1 R hR n hn hlarge z p hz hp₁ hp₂
  have hc := actualSchurLowerOffDiagonal_sub_fourier_bound38V1 R hR n hn hlarge z p hz hp₁ hp₂
  have hbAt : bAt n z p = actualSchurCoefficientAfterDext31 n
      (true, resonantIndex n) (false, resonantIndex n) (z, p) := rfl
  have hcAt : cAt n z p = actualSchurCoefficientAfterDext31 n
      (false, resonantIndex n) (true, resonantIndex n) (z, p) := rfl
  have hC0 : 2 * freeResolventSchurUniformConstant ^ 2 *
        freeResolventComplementaryInverseUniformConstant22 * physicalH1MultiplierConstant ≤
      |2 * freeResolventSchurUniformConstant ^ 2 *
        freeResolventComplementaryInverseUniformConstant22 * physicalH1MultiplierConstant| + 1 := by
    have := le_abs_self (2 * freeResolventSchurUniformConstant ^ 2 *
        freeResolventComplementaryInverseUniformConstant22 * physicalH1MultiplierConstant)
    linarith
  have hmono : 2 * freeResolventSchurUniformConstant ^ 2 *
        freeResolventComplementaryInverseUniformConstant22 * physicalH1MultiplierConstant * R ^ 4 /
        |(n : ℝ)| ^ 2 ≤
      (|2 * freeResolventSchurUniformConstant ^ 2 *
        freeResolventComplementaryInverseUniformConstant22 * physicalH1MultiplierConstant| + 1) *
        R ^ 4 / |(n : ℝ)| ^ 2 := by
    have h1 : 2 * freeResolventSchurUniformConstant ^ 2 *
        freeResolventComplementaryInverseUniformConstant22 * physicalH1MultiplierConstant * R ^ 4 ≤
        (|2 * freeResolventSchurUniformConstant ^ 2 *
          freeResolventComplementaryInverseUniformConstant22 * physicalH1MultiplierConstant| + 1) *
          R ^ 4 :=
      mul_le_mul_of_nonneg_right hC0 (by positivity)
    exact div_le_div_of_nonneg_right h1 (by positivity)
  constructor
  · rw [hbAt, ← physicalH1ComplexCarrierToL2Actual22_fourier p.1 n]
    exact le_trans hb hmono
  · rw [hcAt, ← physicalH1ComplexCarrierToL2Actual22_fourier p.2 (-n)]
    exact le_trans hc hmono

end NlsGge.ThirdConsultation.S
