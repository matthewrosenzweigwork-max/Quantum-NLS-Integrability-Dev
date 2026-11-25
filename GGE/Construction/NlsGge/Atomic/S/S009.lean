import NlsGge.Schur.FreeResolventPotentialColumnRowOperatorBoundsAfterScalarNormPrerequisite
import NlsGge.Schur.FreeResolventDVDHilbertSchmidtFromEnergyAlias
import NlsGge.Schur.FreeResolventPotentialResonantNormConsumersAfterScalarNormPrerequisite
import NlsGge.Schur.ResonantParityPairBasisAction
import NlsGge.Atomic.S.S005

                                                                                                                                                                                                                                                                                                                                                                                                                  
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

def schurPairH1Norm (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) : ℝ :=
  ‖(physicalSobolevL2 1 u₁ hu₁, physicalSobolevL2 1 u₂ hu₂)‖

def schurDVD (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ParityPair n →L[ℂ] ParityPair n :=
  (schurD n z hz).comp ((schurV u₁ u₂ hu₁ hu₂ n).comp (schurD n z hz))

theorem complementarySandwich_isHS :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ), n ≠ 0 →
      ∀ (R : ℝ) (u₁ u₂ : PhysicalL2)
        (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
        (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)),
        schurPairH1Norm u₁ u₂ hu₁ hu₂ ≤ R →
        ∀ (z : ℂ) (hz : z ∈ spectralDisk n),
          IsComplexHilbertSchmidt (schurDVD u₁ u₂ hu₁ hu₂ n z hz) ∧
          complexHilbertSchmidtNorm (schurDVD u₁ u₂ hu₁ hu₂ n z hz) ≤
            C * R / |(n : ℝ)| := by
  refine ⟨1 + 2 * Real.sqrt uniformConvolutionConstant, by positivity, ?_⟩
  intro n hn R u₁ u₂ hu₁ hu₂ hR z hz
  have hH := freeResolventPotentialFreeResolvent_isComplexHilbertSchmidt_from_matrix_energy
    u₁ u₂ hu₁ hu₂ n z hz
  have hDVD : schurDVD u₁ u₂ hu₁ hu₂ n z hz =
      freeResolventPotentialFreeResolventOperator u₁ u₂ hu₁ hu₂ n z hz := rfl
  rw [hDVD]
  refine ⟨hH.1, hH.2.trans ?_⟩
  have h1 : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R := by
    have := norm_fst_le (physicalSobolevL2 1 u₁ hu₁, physicalSobolevL2 1 u₂ hu₂)
    exact this.trans hR
  have h2 : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R := by
    have := norm_snd_le (physicalSobolevL2 1 u₁ hu₁, physicalSobolevL2 1 u₂ hu₂)
    exact this.trans hR
  have hR0 : 0 ≤ R := (norm_nonneg _).trans h1
  have hn0 : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  have hK0 := uniformConvolutionConstant_nonneg
  have hsq : ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 + ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2 ≤ 2 * R ^ 2 := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2, pow_le_pow_left₀ (norm_nonneg _) h2 2]
  have hden : (n : ℝ) ^ 2 ≤ 1 + (n : ℝ) ^ 2 := by linarith
  have hRHS0 : 0 ≤ (1 + 2 * Real.sqrt uniformConvolutionConstant) * R / |(n : ℝ)| := by positivity
  have hin : 2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2) *
      (‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 + ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) ≤
      (2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)|) ^ 2 := by
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
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
  have hmid : Real.sqrt (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2) *
      (‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 + ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2)) ≤
      2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)| := by
    refine (Real.sqrt_le_sqrt hin).trans ?_
    rw [Real.sqrt_sq (by positivity)]
  refine hmid.trans ?_
  have : 2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)| ≤
      (1 + 2 * Real.sqrt uniformConvolutionConstant) * R / |(n : ℝ)| := by
    apply div_le_div_of_nonneg_right _ hn0.le
    nlinarith [hR0]
  exact this

end NlsGge.ThirdConsultation.S
