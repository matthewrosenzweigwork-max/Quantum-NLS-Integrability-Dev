import NlsGge.ThirdConsultation.S.Round4

                                                                                                              
                                                                                                                
                                                                                                                                                 
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem complementaryInteraction_square_small :
    0 < complementaryInteractionConstant ∧
      ∀ (R : ℝ) (u₁ u₂ : PhysicalL2)
        (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
        (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)),
      ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R →
      ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R →
      ∀ (n : ℤ), n ≠ 0 →
      ∀ (z : ℂ) (hz : z ∈ spectralDisk n),
        ‖interaction n z hz u₁ u₂ hu₁ hu₂‖ ≤
            complementaryInteractionConstant * R ∧
        ‖(interaction n z hz u₁ u₂ hu₁ hu₂).comp
            (interaction n z hz u₁ u₂ hu₁ hu₂)‖ ≤
            (complementaryInteractionConstant / 2) * R ^ 2 / |(n : ℝ)| ∧
        (complementaryInteractionConstant * R ^ 2 ≤ |(n : ℝ)| →
          ‖(interaction n z hz u₁ u₂ hu₁ hu₂).comp
              (interaction n z hz u₁ u₂ hu₁ hu₂)‖ ≤ (1 / 2 : ℝ)) := by
  have hm := physicalH1MultiplierConstant_pos
  have hK0 := uniformConvolutionConstant_nonneg
  have hc2 : 2 * Real.sqrt uniformConvolutionConstant ≤ freeResolventSchurUniformConstant :=
    le_max_right _ _
  have hc4 : 0 ≤ 4 * Real.sqrt 2 := by positivity
  have hcpos : 0 ≤ freeResolventSchurUniformConstant := le_trans (by positivity) hc2
  have hCpos : 0 < complementaryInteractionConstant := by
    unfold complementaryInteractionConstant; positivity
  refine ⟨hCpos, ?_⟩
  intro R u₁ u₂ hu₁ hu₂ h1 h2 n hn z hz
  have hR0 : 0 ≤ R := (norm_nonneg _).trans h1
  have hn0 : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  let V : ParityPair n →L[ℂ] ParityPair n := coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let Q : ParityPair n →L[ℂ] ParityPair n := freeResolventComplementaryProjectionTransported n
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let DVD : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
  have hD : ‖D‖ ≤ 1 := by
    let E := parityPairRepr n
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖E.symm (freeResolventSquare n z hz (E x))‖ ≤ 1 * ‖x‖
    calc
      ‖E.symm (freeResolventSquare n z hz (E x))‖ =
          ‖freeResolventSquare n z hz (E x)‖ := E.symm.norm_map _
      _ ≤ ‖freeResolventSquare n z hz‖ * ‖E x‖ :=
        (freeResolventSquare n z hz).le_opNorm _
      _ ≤ 1 * ‖x‖ := by
        rw [E.norm_map]
        gcongr
        exact freeResolventSquare_norm_le_one n z hz
  have hQ : ‖Q‖ ≤ 1 := freeResolventComplementaryProjectionTransported_norm_le_one n
  have hV : ‖V‖ ≤ 2 * physicalH1MultiplierConstant * R :=
    coveredH1ParityPairPotential_norm_bound u₁ u₂ hu₁ hu₂ n R hR0 h1 h2
  have hVn : 0 ≤ ‖V‖ := ContinuousLinearMap.opNorm_nonneg V
  have hA : ‖interaction n z hz u₁ u₂ hu₁ hu₂‖ ≤ 2 * physicalH1MultiplierConstant * R := by
    change ‖D.comp (V.comp Q)‖ ≤ _
    calc ‖D.comp (V.comp Q)‖ ≤ ‖D‖ * ‖V.comp Q‖ := D.opNorm_comp_le _
      _ ≤ ‖D‖ * (‖V‖ * ‖Q‖) :=
        mul_le_mul_of_nonneg_left (V.opNorm_comp_le Q) (ContinuousLinearMap.opNorm_nonneg _)
      _ ≤ 1 * (‖V‖ * 1) := by gcongr
      _ ≤ _ := by linarith
  -- DVD bound
  have hHS := freeResolventPotentialFreeResolvent_isComplexHilbertSchmidt_from_matrix_energy
    u₁ u₂ hu₁ hu₂ n z hz
  have hsq : ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 + ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2 ≤ 2 * R ^ 2 := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2, pow_le_pow_left₀ (norm_nonneg _) h2 2]
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hden : (n : ℝ) ^ 2 ≤ 1 + (n : ℝ) ^ 2 := by linarith
  have hin : 2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2) *
      (‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 + ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) ≤
      (2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)|) ^ 2 := by
    have e : (2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)|) ^ 2 =
        4 * uniformConvolutionConstant * R ^ 2 / (n : ℝ) ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hK0, sq_abs]; ring
    rw [e]
    calc 2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2) *
          (‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 + ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2)
        ≤ 2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2) * (2 * R ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ 2 * uniformConvolutionConstant / (n : ℝ) ^ 2 * (2 * R ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact div_le_div_of_nonneg_left (by positivity) hn2 hden
      _ = 4 * uniformConvolutionConstant * R ^ 2 / (n : ℝ) ^ 2 := by ring
  have hmid : complexHilbertSchmidtNorm DVD ≤ 2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)| := by
    refine hHS.2.trans ?_
    refine (Real.sqrt_le_sqrt hin).trans ?_
    rw [Real.sqrt_sq (by positivity)]
  have hDVD : ‖DVD‖ ≤ freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
    refine (complexHilbertSchmidt_opNorm_le DVD hHS.1).trans (hmid.trans ?_)
    apply div_le_div_of_nonneg_right _ hn0.le
    exact mul_le_mul_of_nonneg_right hc2 hR0
  have hfactor : (interaction n z hz u₁ u₂ hu₁ hu₂).comp (interaction n z hz u₁ u₂ hu₁ hu₂) =
      DVD.comp (V.comp Q) :=
    freeResolventComplementaryPotentialA_sq_factorization u₁ u₂ hu₁ hu₂ n z hz
  have hA2 : ‖(interaction n z hz u₁ u₂ hu₁ hu₂).comp (interaction n z hz u₁ u₂ hu₁ hu₂)‖ ≤
      (complementaryInteractionConstant / 2) * R ^ 2 / |(n : ℝ)| := by
    rw [hfactor]
    have h1' : ‖DVD.comp (V.comp Q)‖ ≤ ‖DVD‖ * (‖V‖ * ‖Q‖) :=
      (DVD.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left (V.opNorm_comp_le Q) (ContinuousLinearMap.opNorm_nonneg _))
    have h2' : ‖DVD‖ * (‖V‖ * ‖Q‖) ≤
        (freeResolventSchurUniformConstant * R / |(n : ℝ)|) * (2 * physicalH1MultiplierConstant * R) := by
      calc ‖DVD‖ * (‖V‖ * ‖Q‖) ≤ ‖DVD‖ * (‖V‖ * 1) := by gcongr
        _ ≤ ‖DVD‖ * (2 * physicalH1MultiplierConstant * R) := by
          rw [mul_one]; gcongr
        _ ≤ _ := by gcongr
    refine h1'.trans (h2'.trans ?_)
    have : (freeResolventSchurUniformConstant * R / |(n : ℝ)|) * (2 * physicalH1MultiplierConstant * R) =
        (2 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant) * R ^ 2 / |(n : ℝ)| := by
      field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ hn0.le
    have : 2 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant ≤
        complementaryInteractionConstant / 2 := by
      unfold complementaryInteractionConstant; nlinarith [mul_pos hm hm]
    exact mul_le_mul_of_nonneg_right this (sq_nonneg R)
  refine ⟨?_, hA2, ?_⟩
  · refine hA.trans ?_
    unfold complementaryInteractionConstant
    have hpos : 0 ≤ (1 + 4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant) * R := by positivity
    linarith [hpos]
  · intro hlarge
    refine hA2.trans ?_
    rw [div_le_iff₀ hn0]
    nlinarith [hlarge]

end NlsGge.ThirdConsultation.S
