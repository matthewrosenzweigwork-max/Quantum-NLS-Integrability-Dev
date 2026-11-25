import Mathlib
import NlsGge.Schur.ActualSchurOwnModeDerivative38V1
import NlsGge.Schur.ActualSchurOwnModeVariation38V1
import NlsGge.Schur.ActualSchurPotentialVariation38V1
import NlsGge.Schur.ActualSchurCoefficientJointAnalyticV2_31
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                                                                                                        
                                                                                                                                                                                                 
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

                                                                                          
                                                                                                   
                                          
theorem s030_fderiv_of_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (g : E → F) (p h : E) (A : F)
    (hd : DifferentiableAt ℂ g p) (hA : HasDerivAt (fun t : ℂ => g (p + t • h)) A 0) :
    fderiv ℂ g p h = A := by
  have hl : HasDerivAt (fun t : ℂ => p + t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add p
  have hg2 : HasFDerivAt g (fderiv ℂ g p) (p + (0 : ℂ) • h) := by
    rw [zero_smul, add_zero]
    exact hd.hasFDerivAt
  exact (hA.unique (hg2.comp_hasDerivAt (0 : ℂ) hl)).symm

theorem schurOwnMode_entry_bound :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (R : ℝ) (n : ℤ) (z : ℂ) (p : SchurPair),
        schurParameterDomain K R n z p →
        ‖ownDerivative (bAt n z) n p - 1‖ +
          ‖ownDerivative (alphaAt n z) n p‖ ≤ C * R ^ 4 / |(n : ℝ)| ^ 2 := by
  have hI : 0 < freeResolventComplementaryInverseUniformConstant22 :=
    freeResolventComplementaryInverseUniformConstant22_posV2_31
  have hS : 0 < freeResolventSchurUniformConstant := by
    unfold freeResolventSchurUniformConstant
    positivity
  refine ⟨2 * (freeResolventComplementaryInverseUniformConstant22 ^ 2 *
      freeResolventSchurUniformConstant ^ 2),
    max 1 (4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant),
    mul_pos two_pos (mul_pos (pow_pos hI 2) (pow_pos hS 2)),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R n z p hdom
  obtain ⟨hR, hn0, hK, hz, hp₁, hp₂⟩ := hdom
  have hn : 1 ≤ |(n : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast h1
  have hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg R)) hK
  -- differentiability in the pair at fixed z, from the joint analyticity on the closed domain
  obtain ⟨hA, hB, -, -⟩ := actualSchurCoefficientsJointAnalyticV2_31 R hR n hn hlarge
  have hpair : DifferentiableAt ℂ (fun q : SchurPair => (z, q)) p :=
    (differentiableAt_const z).prodMk differentiableAt_id
  have hda : DifferentiableAt ℂ (alphaAt n z) p :=
    ((hA (z, p) ⟨hz, hp₁, hp₂⟩).differentiableAt).comp p hpair
  have hdb : DifferentiableAt ℂ (bAt n z) p :=
    ((hB (z, p) ⟨hz, hp₁, hp₂⟩).differentiableAt).comp p hpair
  -- fixed-z line derivatives of both coefficients along the own-mode direction
  have hbline := actualSchurCoefficient_hasDerivAt_potentialVariation38V1 R hR n hn hlarge z hz p
    hp₁ hp₂ (actualH1ModeVector38 n, 0) (true, resonantIndex n) (false, resonantIndex n)
  have haline := actualSchurCoefficient_hasDerivAt_potentialVariation38V1 R hR n hn hlarge z hz p
    hp₁ hp₂ (actualH1ModeVector38 n, 0) (true, resonantIndex n) (true, resonantIndex n)
  have hfb := s030_fderiv_of_line (bAt n z) p (actualH1ModeVector38 n, 0) _ hdb hbline
  have hfa := s030_fderiv_of_line (alphaAt n z) p (actualH1ModeVector38 n, 0) _ hda haline
  -- production entrywise bounds with the resonant entries of H_n
  have hbb := actualSchurOwnModeVariation_entry_bound38 R hR n hn hlarge z hz p hp₁ hp₂ true false
  have hba := actualSchurOwnModeVariation_entry_bound38 R hR n hn hlarge z hz p hp₁ hp₂ true true
  rw [actualOwnModeVariation38_resonant_plusMinus] at hbb
  rw [actualOwnModeVariation38_resonant_other n true true (by simp), sub_zero] at hba
  unfold ownDerivative ownDirection
  rw [hfb, hfa]
  have hdsum : actualSchurOwnModeScale38 R n + actualSchurOwnModeScale38 R n =
      2 * (freeResolventComplementaryInverseUniformConstant22 ^ 2 *
        freeResolventSchurUniformConstant ^ 2) * R ^ 4 / |(n : ℝ)| ^ 2 := by
    unfold actualSchurOwnModeScale38
    ring
  exact le_trans (add_le_add hbb hba) (le_of_eq hdsum)

end NlsGge.ThirdConsultation.S
