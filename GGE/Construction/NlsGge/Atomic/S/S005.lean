import NlsGge.Schur.FreeResolventPotentialColumnRowOperatorBoundsAfterScalarNormPrerequisite
import NlsGge.Schur.FreeResolventDVDHilbertSchmidtFromEnergyAlias
import NlsGge.Schur.FreeResolventPotentialResonantNormConsumersAfterScalarNormPrerequisite
import NlsGge.Schur.ResonantParityPairBasisAction

                                                                                                                                                                                                                                                                                                                                                                                                                                                      
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S


def schurD (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ParityPair n →L[ℂ] ParityPair n :=
  freeResolventParityPair n z hz

def schurV (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) : ParityPair n →L[ℂ] ParityPair n :=
  coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n

def basisMinus (n : ℤ) : ParityPair n :=
  parityPairVector n (false, resonantIndex n)

theorem resolvent_resonantColumn_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ), n ≠ 0 →
      ∀ (R : ℝ) (u₁ u₂ : PhysicalL2)
        (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
        (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)),
        ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R →
        ∀ (z : ℂ) (hz : z ∈ spectralDisk n),
          ‖schurD n z hz (schurV u₁ u₂ hu₁ hu₂ n (basisMinus n))‖ ≤
            C * R / |(n : ℝ)| := by
  refine ⟨Real.sqrt 2, by positivity, ?_⟩
  intro n hn R u₁ u₂ hu₁ hu₂ hR z hz
  have h := freeResolventPotentialColumn_false_resonant_norm_sq_le_from_prerequisites
    u₁ u₂ hu₁ hu₂ n hn z hz
  have hP' : resonantParityPair n (parityPairVector n (false, resonantIndex n)) =
      parityPairVector n (false, resonantIndex n) := by
    rw [resonantParityPair_apply_basis]; simp
  have e : freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz (parityPairVector n (false, resonantIndex n)) =
      schurD n z hz (schurV u₁ u₂ hu₁ hu₂ n (basisMinus n)) := by
    unfold freeResolventPotentialColumn schurD schurV basisMinus
    simp only [ContinuousLinearMap.comp_apply]
    rw [hP']
  rw [e] at h
  have hn0 : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hRHS0 : 0 ≤ Real.sqrt 2 * R / |(n : ℝ)| := by positivity
  have hsq : (Real.sqrt 2 * R / |(n : ℝ)|) ^ 2 = 2 / (n : ℝ) ^ 2 * R ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), sq_abs]; ring
  have h2 : ‖schurD n z hz (schurV u₁ u₂ hu₁ hu₂ n (basisMinus n))‖ ^ 2 ≤
      (Real.sqrt 2 * R / |(n : ℝ)|) ^ 2 := by
    rw [hsq]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact pow_le_pow_left₀ (norm_nonneg _) hR 2
  exact (sq_le_sq₀ (norm_nonneg _) hRHS0).1 h2

end NlsGge.ThirdConsultation.S
