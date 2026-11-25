import NlsGge.Spectral.ActualComplexZsDysonTermFactorialEntryBoundV9
import NlsGge.Spectral.ActualContinuousPotentialCompactNormBoundV2
import NlsGge.Spectral.ActualComplexZsDysonFiniteTermEntireContinuousPotentialV3
import NlsGge.Spectral.RealPowerDivisionProductPrerequisiteV1
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

theorem differentiableOn_actualComplexZsDysonTsum_on_ball_of_continuousOn
    (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hU : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖u s‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) (i j : Fin 2) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∑' n : ℕ, actualComplexZsDysonTerm u z n t i j)
      (Metric.ball 0 R) := by
  let majorant : ℕ → ℝ := fun n => (2 * (2 * (R + C))) ^ n / (n.factorial : ℝ)
  have hsum : Summable majorant := by
    simpa [majorant] using
      (NormedSpace.expSeries_div_hasSum_exp (2 * (2 * (R + C)))).summable
  apply Complex.differentiableOn_tsum_of_summable_norm hsum
  · intro n z hz
    exact (analyticOnNhd_actualComplexZsDysonTerm_of_continuousOn
      u hu n t ht i j z (Set.mem_univ z)).differentiableAt.differentiableWithinAt
  · exact Metric.isOpen_ball
  · intro n z hz
    have hz' : ‖z‖ ≤ R := by
      have hzball := Metric.mem_ball.mp hz
      simpa [dist_eq_norm] using le_of_lt hzball
    have hterm := actualComplexZsDysonTerm_entry_factorial_bound
      u z R C hz' hR hU hC n t ht i j
    have htPow : t ^ n ≤ (2 : ℝ) ^ n :=
      pow_le_pow_left₀ ht.1 ht.2 n
    have hcoef : 0 ≤ ((2 * (R + C)) ^ n / (n.factorial : ℝ)) := by positivity
    calc
      ‖actualComplexZsDysonTerm u z n t i j‖ ≤
          ((2 * (R + C)) ^ n / (n.factorial : ℝ)) * t ^ n := hterm
      _ ≤ ((2 * (R + C)) ^ n / (n.factorial : ℝ)) * (2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left htPow hcoef
      _ = majorant n := by
          dsimp [majorant]
          calc
            ((2 * (R + C)) ^ n / (n.factorial : ℝ)) * (2 : ℝ) ^ n =
                ((2 * (R + C)) * 2) ^ n / (n.factorial : ℝ) := by
              exact real_pow_div_mul_pow (2 * (R + C)) 2 (n.factorial : ℝ) n
            _ = (2 * (2 * (R + C))) ^ n / (n.factorial : ℝ) := by
              congr 1
              ring

theorem analyticOnNhd_actualComplexZsDysonTsum_of_continuousOn
    (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) (i j : Fin 2) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∑' n : ℕ, actualComplexZsDysonTerm u z n t i j)
      Set.univ := by
  obtain ⟨C, hC, hU⟩ := exists_nonneg_actualPotential_norm_bound u hu
  intro z hz
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hzball : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp [R]
    simp
  have hdiff := differentiableOn_actualComplexZsDysonTsum_on_ball_of_continuousOn
    u hu R C hR.le hC hU t ht i j
  exact hdiff.analyticAt (Metric.isOpen_ball.mem_nhds hzball)

end NlsGge.SpectralFoundations
