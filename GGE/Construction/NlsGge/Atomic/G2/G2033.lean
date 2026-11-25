import Mathlib
import NlsGge.GK38.XiSqCenteredCandidate
import NlsGge.GK38.XiSqCanonical
import NlsGge.GK38.XiSqLocal
import NlsGge.GK38.IsolatingTopology

                                                                                                                                
                                                                                                                                                            
                                                                                                                                                           
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G2_033 (n : ℤ) :
    AnalyticOnNhd ℂ (xiSq38 n) gkW ∧
    ∀ φ ∈ gkW,
      gamma2 φ n*xiSq38 n φ = 4*gkActionC38 φ n ∧
      (gamma2 φ n ≠ 0 → xiSq38 n φ = 4*gkActionC38 φ n/gamma2 φ n) ∧
      (gamma2 φ n = 0 → xiSq38 n φ = a5Chi38 n (φ,tauN φ n)) := by
  refine ⟨xiSq38_analytic n, fun φ hφ => ⟨xiSq38_multiplied n φ hφ,
    fun hne => xiSq38_eq_quotient n φ hφ hne, fun h0 => ?_⟩⟩
  obtain ⟨V, hV, hVW, hVo, -, C, R, hf⟩ := local_isolatingFamily φ hφ
  have hφV : φ ∈ V := mem_of_mem_nhds hV
  have hxi := a5CenteredLocalXi_eq_candidate38 n (xiSq38 n) (xiSq38_spec n) V hVo hVW C R hf φ hφV
  rw [← hxi]
  have hfφ := hf φ hφV
  have hr := isolating_radius_pos38 hfφ n
  -- tau lies in the isolating ball
  have hτ : tauN φ n ∈ ball (C n) (R n) := by
    obtain ⟨c, N, hg, hs⟩ := hfφ
    have hseg := (hs.1 n).1
    have hg2 := gamma2_value38 φ hφ n
    rw [h0] at hg2
    have hlam : lamPlus φ n = lamMinus φ n := by
      have : (lamPlus φ n - lamMinus φ n) ^ 2 = 0 := hg2.symm
      exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
    have ht := tauN_value38 φ hφ n
    rw [hlam] at ht
    have : tauN φ n = lamMinus φ n := by rw [ht]; ring
    rw [this]
    exact hseg (left_mem_segment ℝ _ _)
  -- kernel at gamma2 = 0
  have hker : ∀ z ∈ sphere (C n) (R n), a5CenteredKernel38 n (φ, z) =
      (1 / (8 * Complex.I)) * ((z - tauN φ n)⁻¹ • a5Chi38 n (φ, z)) := by
    intro z hz
    have hp : (φ, z) ∈ rootDomain38 := ⟨hφ, fixed_sphere_subset φ C R hfφ n hz⟩
    obtain ⟨hw, hq, hplus, hsq⟩ := a5BoundaryQ_properties38 n (φ, z) hp
    have hq1 : a5BoundaryQ38 n (φ, z) = 1 := by
      have h1 : a5BoundaryQ38 n (φ, z) ^ 2 = 1 := by
        simpa [h0] using hsq
      have hre := Lib.re_sqrt_nonneg (1 - (gamma2 φ n / 4) / (tauN φ n - z) ^ 2)
      change 0 ≤ (a5BoundaryQ38 n (φ, z)).re at hre
      have hfac : (a5BoundaryQ38 n (φ, z) - 1) * (a5BoundaryQ38 n (φ, z) + 1) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.1 hfac with h | h
      · exact sub_eq_zero.1 h
      · exfalso
        apply hplus
        linear_combination h
    unfold a5CenteredKernel38 a5CenteredAnalyticTerm38
    rw [hq1, h0]
    have hw' : tauN φ n - z ≠ 0 := hw
    have hz' : z - tauN φ n ≠ 0 := fun h => hw' (by linear_combination -h)
    simp only [zero_mul, add_zero, smul_eq_mul]
    field_simp
    ring
  have hcirc : circleIntegral (fun z => a5CenteredKernel38 n (φ, z)) (C n) (R n) =
      (1 / (8 * Complex.I)) * ((2 * Real.pi * Complex.I) * a5Chi38 n (φ, tauN φ n)) := by
    rw [circleIntegral.integral_congr hr.le hker]
    rw [circleIntegral.integral_const_mul]
    congr 1
    refine Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (s := (∅ : Set ℂ)) countable_empty hτ ?_ ?_
    · intro z hz
      have hdom := a5OwnClosedBall_omittedDomain38 φ hφ C R hfφ n z hz
      exact (AnalyticAt.comp (g := a5Chi38 n) (f := fun w : ℂ => (φ, w))
        (a5Chi_analytic38 n _ hdom) (analyticAt_const.prod analyticAt_id)).continuousAt.continuousWithinAt
    · intro z hz
      have hdom := a5OwnClosedBall_omittedDomain38 φ hφ C R hfφ n z (ball_subset_closedBall hz.1)
      exact (AnalyticAt.comp (g := a5Chi38 n) (f := fun w : ℂ => (φ, w))
        (a5Chi_analytic38 n _ hdom) (analyticAt_const.prod analyticAt_id)).differentiableAt
  unfold a5CenteredLocalXi38
  rw [hcirc]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

end
end NlsGge.GKDefinitionDesign
