import Mathlib
import NlsGge.ThirdConsultation.S.S006Host06
import NlsGge.Atomic.S.S009
import NlsGge.Schur.FreeResolventPotentialColumnRowOperatorBoundsAfterScalarNormPrerequisite
import NlsGge.Schur.FreeResolventPotentialResonantNormConsumersAfterScalarNormPrerequisite
import NlsGge.Schur.ResonantParityPairBasisAction
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1

                                                                                           
                                                                                                                      
                                                                                                      
                                                                                                            
                                                                                                                      
                                                                                                                              
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem norm_le_sqrt_two_mul_div_of_sq_le
    (n : ℤ) (hn : n ≠ 0) (R c t : ℝ) (hc0 : 0 ≤ c) (hcR : c ≤ R) (ht0 : 0 ≤ t)
    (ht : t ^ 2 ≤ (2 / (n : ℝ) ^ 2) * c ^ 2) :
    t ≤ Real.sqrt 2 * R / |(n : ℝ)| := by
  have hR0 : 0 ≤ R := hc0.trans hcR
  have hn0 : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  have hRHS0 : 0 ≤ Real.sqrt 2 * R / |(n : ℝ)| := by positivity
  have hsq : (Real.sqrt 2 * R / |(n : ℝ)|) ^ 2 = 2 / (n : ℝ) ^ 2 * R ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), sq_abs]; ring
  have hc2 : (2 / (n : ℝ) ^ 2) * c ^ 2 ≤ (2 / (n : ℝ) ^ 2) * R ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0 hcR 2) (by positivity)
  exact (sq_le_sq₀ ht0 hRHS0).1 (by rw [hsq]; exact ht.trans hc2)

theorem sqrt_two_div_le_of_sq_le
    (n : ℤ) (hn : n ≠ 0) (R c : ℝ) (hc0 : 0 ≤ c) (hcR : c ≤ R) :
    Real.sqrt ((2 / (n : ℝ) ^ 2) * c ^ 2) ≤ Real.sqrt 2 * R / |(n : ℝ)| := by
  have hR0 : 0 ≤ R := hc0.trans hcR
  have hn0 : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  have hRHS0 : 0 ≤ Real.sqrt 2 * R / |(n : ℝ)| := by positivity
  have hsq : (Real.sqrt 2 * R / |(n : ℝ)|) ^ 2 = 2 / (n : ℝ) ^ 2 * R ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), sq_abs]; ring
  have hc2 : (2 / (n : ℝ) ^ 2) * c ^ 2 ≤ (2 / (n : ℝ) ^ 2) * R ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0 hcR 2) (by positivity)
  exact Real.sqrt_le_iff.2 ⟨hRHS0, by rw [hsq]; exact hc2⟩

theorem resonantParityPair_basisPlus (n : ℤ) :
    resonantParityPair n (basisPlus n) = basisPlus n := by
  unfold basisPlus
  rw [resonantParityPair_apply_basis]
  simp

theorem resonantParityPair_basisMinus (n : ℤ) :
    resonantParityPair n (basisMinus n) = basisMinus n := by
  unfold basisMinus
  rw [resonantParityPair_apply_basis]
  simp

theorem innerSL_comp_opNorm_le_adjoint_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (e : H) :
    ‖(innerSL ℂ e).comp T‖ ≤ ‖T.adjoint e‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, ← ContinuousLinearMap.adjoint_inner_left]
  exact norm_inner_le_norm _ _

theorem resonantPotentialFreeResolventRow_adjoint_eq_of_fixed
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (e : ParityPair n)
    (he : resonantParityPair n e = e) :
    (resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz).adjoint e =
      ((schurV u₁ u₂ hu₁ hu₂ n).comp (schurD n z hz)).adjoint e := by
  unfold resonantPotentialFreeResolventRow schurD schurV
  rw [ContinuousLinearMap.adjoint_comp (resonantParityPair n), ContinuousLinearMap.comp_apply,
    resonantParityPair_adjoint38, he]

theorem resolvent_resonantPlusColumn_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ), n ≠ 0 →
      ∀ (R : ℝ) (u₁ u₂ : PhysicalL2)
        (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
        (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)),
        ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R →
        ∀ (z : ℂ) (hz : z ∈ spectralDisk n),
          ‖schurD n z hz (schurV u₁ u₂ hu₁ hu₂ n (basisPlus n))‖ ≤
            C * R / |(n : ℝ)| := by
  refine ⟨Real.sqrt 2, by positivity, ?_⟩
  intro n hn R u₁ u₂ hu₁ hu₂ hR z hz
  have h : ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz (basisPlus n)‖ ^ 2 ≤
      (2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2 :=
    freeResolventPotentialColumn_true_resonant_norm_sq_le_from_prerequisites
      u₁ u₂ hu₁ hu₂ n hn z hz
  have e : freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz (basisPlus n) =
      schurD n z hz (schurV u₁ u₂ hu₁ hu₂ n (basisPlus n)) := by
    unfold freeResolventPotentialColumn schurD schurV
    simp only [ContinuousLinearMap.comp_apply]
    rw [resonantParityPair_basisPlus]
  rw [e] at h
  exact norm_le_sqrt_two_mul_div_of_sq_le n hn R _ _ (norm_nonneg _) hR (norm_nonneg _) h

theorem resolvent_resonantPlusRow_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ), n ≠ 0 →
      ∀ (R : ℝ) (u₁ u₂ : PhysicalL2)
        (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
        (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)),
        ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R →
        ∀ (z : ℂ) (hz : z ∈ spectralDisk n),
          ‖(innerSL ℂ (basisPlus n)).comp
              ((schurV u₁ u₂ hu₁ hu₂ n).comp (schurD n z hz))‖ ≤
            C * R / |(n : ℝ)| := by
  refine ⟨Real.sqrt 2, by positivity, ?_⟩
  intro n hn R u₁ u₂ hu₁ hu₂ hR z hz
  have hadj : ‖(resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz).adjoint (basisPlus n)‖ ^ 2 ≤
      (2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 :=
    resonantPotentialFreeResolventRow_true_resonant_adjoint_norm_sq_le_from_prerequisites
      u₁ u₂ hu₁ hu₂ n hn z hz
  have hfun : ‖(innerSL ℂ (basisPlus n)).comp ((schurV u₁ u₂ hu₁ hu₂ n).comp (schurD n z hz))‖ ≤
      ‖(resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz).adjoint (basisPlus n)‖ := by
    rw [resonantPotentialFreeResolventRow_adjoint_eq_of_fixed u₁ u₂ hu₁ hu₂ n z hz (basisPlus n)
      (resonantParityPair_basisPlus n)]
    exact innerSL_comp_opNorm_le_adjoint_apply _ _
  exact hfun.trans (norm_le_sqrt_two_mul_div_of_sq_le n hn R _ _ (norm_nonneg _) hR (norm_nonneg _) hadj)

theorem resolvent_resonantMinusRow_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ), n ≠ 0 →
      ∀ (R : ℝ) (u₁ u₂ : PhysicalL2)
        (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
        (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)),
        ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R →
        ∀ (z : ℂ) (hz : z ∈ spectralDisk n),
          ‖(innerSL ℂ (basisMinus n)).comp
              ((schurV u₁ u₂ hu₁ hu₂ n).comp (schurD n z hz))‖ ≤
            C * R / |(n : ℝ)| := by
  refine ⟨Real.sqrt 2, by positivity, ?_⟩
  intro n hn R u₁ u₂ hu₁ hu₂ hR z hz
  have hadj : ‖(resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz).adjoint (basisMinus n)‖ ^ 2 ≤
      (2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2 :=
    resonantPotentialFreeResolventRow_false_resonant_adjoint_norm_sq_le_from_prerequisites
      u₁ u₂ hu₁ hu₂ n hn z hz
  have hfun : ‖(innerSL ℂ (basisMinus n)).comp ((schurV u₁ u₂ hu₁ hu₂ n).comp (schurD n z hz))‖ ≤
      ‖(resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz).adjoint (basisMinus n)‖ := by
    rw [resonantPotentialFreeResolventRow_adjoint_eq_of_fixed u₁ u₂ hu₁ hu₂ n z hz (basisMinus n)
      (resonantParityPair_basisMinus n)]
    exact innerSL_comp_opNorm_le_adjoint_apply _ _
  exact hfun.trans (norm_le_sqrt_two_mul_div_of_sq_le n hn R _ _ (norm_nonneg _) hR (norm_nonneg _) hadj)

theorem resolvent_resonant_rows_columns :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (n : ℤ), n ≠ 0 →
      ∀ (u₁ u₂ : PhysicalL2)
        (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
        (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)),
        schurPairH1Norm u₁ u₂ hu₁ hu₂ ≤ R →
        ∀ (z : ℂ) (hz : z ∈ spectralDisk n),
          ‖(schurD n z hz).comp
              ((schurV u₁ u₂ hu₁ hu₂ n).comp (resonantParityPair n))‖ +
            ‖(resonantParityPair n).comp
              ((schurV u₁ u₂ hu₁ hu₂ n).comp (schurD n z hz))‖ ≤
            C * R / |(n : ℝ)| := by
  refine ⟨4 * Real.sqrt 2, by positivity, ?_⟩
  intro R n hn u₁ u₂ hu₁ hu₂ hpair z hz
  have hpair' : ‖(physicalSobolevL2 1 u₁ hu₁, physicalSobolevL2 1 u₂ hu₂)‖ ≤ R := hpair
  have h1 : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R := (norm_fst_le _).trans hpair'
  have h2 : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R := (norm_snd_le _).trans hpair'
  have hA := freeResolventPotentialColumn_opNorm_bound_from_prerequisites u₁ u₂ hu₁ hu₂ n hn z hz
  have hB := resonantPotentialFreeResolventRow_opNorm_bound_from_prerequisites u₁ u₂ hu₁ hu₂ n hn z hz
  have hcol : ‖(schurD n z hz).comp ((schurV u₁ u₂ hu₁ hu₂ n).comp (resonantParityPair n))‖ =
      ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ := rfl
  have hrow : ‖(resonantParityPair n).comp ((schurV u₁ u₂ hu₁ hu₂ n).comp (schurD n z hz))‖ =
      ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ := rfl
  rw [hcol, hrow]
  have s1 := sqrt_two_div_le_of_sq_le n hn R _ (norm_nonneg _) h1
  have s2 := sqrt_two_div_le_of_sq_le n hn R _ (norm_nonneg _) h2
  have s3 := sqrt_two_div_le_of_sq_le n hn R _ (norm_nonneg _) h1
  have s4 := sqrt_two_div_le_of_sq_le n hn R _ (norm_nonneg _) h2
  have e4 : 4 * Real.sqrt 2 * R / |(n : ℝ)| = 4 * (Real.sqrt 2 * R / |(n : ℝ)|) := by ring
  rw [e4]
  linarith [add_le_add hA hB]

end NlsGge.ThirdConsultation.S
