import Mathlib
import NlsGge.GK38.XiSqPeriod
import NlsGge.GK38.TauGammaCriticalTails
import NlsGge.GK38.TauGammaFiniteBounds
import NlsGge.GK38.TauGammaCriticalAnalytic
import NlsGge.Definitions.PilotInterfaces

                                                                                         
                                                                                            
                                                   
                                                                                           
                                                                                         
                                                                                         
                                                                                                     
                                                                               
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G2042S1
noncomputable section

/-- MS-A (GK (13.2)): the circle integral of `deriv (discrim φ) / canonRoot38 φ` vanishes on every
isolating circle family. -/
theorem zeroPeriod_gkW :
    ∀ φ ∈ gkW, ∀ (C : ℤ → ℂ) (R : ℤ → ℝ), IsolatingFamily38 φ C R → ∀ n : ℤ,
      circleIntegral (fun z : ℂ => deriv (discrim φ) z / canonRoot38 φ z) (C n) (R n) = 0 := by
  intro φ hφ C R hf n
  exact (a5FixedPeriod_zero38 φ hφ C R hf n).2

/-- Companion of `zeroPeriod_gkW` (review item A): the integrand is circle-integrable on every
isolating circle family, so the vanishing of its circle integral is not vacuous under the
totalized `circleIntegral`. Same binders as `zeroPeriod_gkW`. -/
theorem zeroPeriod_gkW_integrable :
    ∀ φ ∈ gkW, ∀ (C : ℤ → ℂ) (R : ℤ → ℝ), IsolatingFamily38 φ C R → ∀ n : ℤ,
      CircleIntegrable (fun z : ℂ => deriv (discrim φ) z / canonRoot38 φ z) (C n) (R n) := by
  intro φ hφ C R hf n
  exact (a5FixedPeriod_zero38 φ hφ C R hf n).1

theorem abs_le_japaneseBracket_G2042 (n : ℤ) : |(n : ℝ)| ≤ japaneseBracket n := by
  unfold japaneseBracket
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (n : ℝ)]

theorem one_le_japaneseBracket_G2042 (n : ℤ) : 1 ≤ japaneseBracket n := by
  unfold japaneseBracket
  have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + (n : ℝ) ^ 2 by nlinarith [sq_nonneg (n : ℝ)])
  rwa [Real.sqrt_one] at h

theorem norm_countingCenter_G2042 (n : ℤ) :
    ‖(n : ℂ) * (Real.pi : ℂ)‖ = |(n : ℝ)| * Real.pi := by
  rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]

/-- MS-B: exported locally uniform growth of the critical roots, with the bracket weight. -/
theorem lamDot_growth_local :
    ∀ φ₀ ∈ gkW, ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ gkW ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ ∈ V, ∀ n : ℤ, ‖lamDot φ n‖ ≤ C * japaneseBracket n := by
  intro φ₀ hφ₀
  obtain ⟨V, hV, hVW, N, hTail⟩ :=
    critical_uniform_tail38 φ₀ hφ₀ (Real.pi / 8) (by positivity)
  obtain ⟨W, hW, B, hB, hBd⟩ := finite_continuous_seq_bound38
    (fun φ n => lamDot φ n) (Finset.Icc (-(N : ℤ)) (N : ℤ)) φ₀
    (fun n _ => (lamDot_analytic38 n φ₀ hφ₀).continuousAt)
  have hpi := Real.pi_pos
  refine ⟨V ∩ W, inter_mem hV hW, fun φ hφ => hVW hφ.1, B + (Real.pi + Real.pi / 8),
    by linarith, ?_⟩
  intro φ hφ n
  have hJ1 := one_le_japaneseBracket_G2042 n
  have hJ0 : 0 ≤ japaneseBracket n := by linarith
  have hBJ : 0 ≤ B * japaneseBracket n := mul_nonneg hB hJ0
  have hPJ : 0 ≤ (Real.pi + Real.pi / 8) * japaneseBracket n := mul_nonneg (by linarith) hJ0
  have hsplit : (B + (Real.pi + Real.pi / 8)) * japaneseBracket n =
      B * japaneseBracket n + (Real.pi * japaneseBracket n + Real.pi / 8 * japaneseBracket n) := by
    ring
  by_cases hn : (N : ℤ) < |n|
  · have h1 : ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 8 := hTail φ hφ.1 n hn
    have h2 : ‖lamDot φ n‖ ≤ ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ +
        ‖(n : ℂ) * (Real.pi : ℂ)‖ := by
      have := norm_add_le (lamDot φ n - (n : ℂ) * (Real.pi : ℂ)) ((n : ℂ) * (Real.pi : ℂ))
      rwa [sub_add_cancel] at this
    rw [norm_countingCenter_G2042] at h2
    have h3 : |(n : ℝ)| * Real.pi ≤ Real.pi * japaneseBracket n := by
      rw [mul_comm Real.pi]
      exact mul_le_mul_of_nonneg_right (abs_le_japaneseBracket_G2042 n) hpi.le
    have h4 : Real.pi / 8 ≤ Real.pi / 8 * japaneseBracket n :=
      le_mul_of_one_le_right (by positivity) hJ1
    linarith
  · have hle : |n| ≤ (N : ℤ) := not_lt.mp hn
    have hnS : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      rw [Finset.mem_Icc]
      exact abs_le.mp hle
    have hb : ‖lamDot φ n‖ ≤ B := hBd φ hφ.2 n hnS
    have hBle : B ≤ B * japaneseBracket n := le_mul_of_one_le_right hB hJ1
    linarith

end
end G2042S1
end NlsGge.GKDefinitionDesign
