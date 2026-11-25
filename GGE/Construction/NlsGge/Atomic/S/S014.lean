import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurRealTypeDeterminant38V1

                                                                                                           
                                                                                                                     
                                                                                                              
                                                                                                          
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem schur_effective_equal_diagonal :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (n : ℤ) (z : ℂ) (p : SchurPair),
      schurParameterDomain K R n z p →
      entryAt n true true z p = entryAt n false false z p := by
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
      nlinarith
    linarith
  exact (actualSchurCoefficient_equal_diagonal38 R (by linarith) n hn hlarge z p hz hp₁ hp₂).symm

end NlsGge.ThirdConsultation.S
