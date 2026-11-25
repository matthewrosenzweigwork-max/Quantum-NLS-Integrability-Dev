import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurBallFullEnergy38V1

                                                                                                          
                                                                            
                                                                                                              
                               
                                                                                                          
                                                                                                                     
                                                                                                    
                                                                                                                  
                                                                                                                   
                                              
set_option autoImplicit false
noncomputable section
open MeasureTheory
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur NlsGge.Measure NlsGge.SpectralFoundations
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.S

theorem relativeBallIntegral_bound (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : BoundedCoefficients lo up) (R : ℝ), 1 ≤ R →
      ∀ N : ℕ, relativeBallIntegralV6 c N R ≤ Real.exp (C * (1 + R) ^ 9) := by
  obtain ⟨C, hC, hball⟩ := actualSchurBallIntegral_fullEnergy38 lo up hl hlu
  refine ⟨C, hC, ?_⟩
  intro c R hR N
  obtain ⟨-, -, hb, hu⟩ := boundedCoefficients_bounds38 c
  have hapos : ∀ n : ℤ, 0 < fullWeightRate c.val n :=
    fun n => fullWeightRate_pos lo up c.val hl hb hu n
  have hF : 0 < freeNormalizer38 c N := by
    unfold freeNormalizer38
    exact Finset.prod_pos fun i _ => div_pos Real.pi_pos (hapos _)
  have hL := hball c R hR N
  have hRHS : (∏ i : Fin (2 * N + 1), ENNReal.ofReal (Real.pi / fullWeightRate c.val (modeIndex N i))) *
      ENNReal.ofReal (Real.exp (C * (1 + R) ^ 9)) =
      ENNReal.ofReal (freeNormalizer38 c N * Real.exp (C * (1 + R) ^ 9)) := by
    rw [ENNReal.ofReal_mul hF.le]
    unfold freeNormalizer38
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (div_pos Real.pi_pos (hapos _)).le)]
  rw [hRHS] at hL
  have hmeas : AEStronglyMeasurable (fun z => Real.exp (-fullEnergy38 c N z))
      ((planeVolume N).restrict (schurH1Ball N R)) :=
    ((continuous_fullEnergy38 c N).neg.rexp).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[(planeVolume N).restrict (schurH1Ball N R)]
      (fun z => Real.exp (-fullEnergy38 c N z)) :=
    Filter.Eventually.of_forall fun z => (Real.exp_pos _).le
  have hI : ∫ z in schurH1Ball N R, Real.exp (-fullEnergy38 c N z) ∂planeVolume N ≤
      freeNormalizer38 c N * Real.exp (C * (1 + R) ^ 9) := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL
  unfold relativeBallIntegralV6
  rw [div_le_iff₀ hF]
  exact hI.trans_eq (mul_comm _ _)

end NlsGge.ThirdConsultation.S
