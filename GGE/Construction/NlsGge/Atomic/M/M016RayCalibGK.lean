import Mathlib
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.ContourAction
import NlsGge.GK38.StdRootBranchesDefs
import NlsGge.Atomic.M.M016RayCalibCore
import NlsGge.Atomic.M.M016RayCutFree

                                                                                                       
                                                                                                                
                                                                                                           
                                    
                                                                                                          
                                                                                                   
                                                                                                                 
                                                                                                 
                                                                                                                   
                                                                     

set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M016ChartAux

theorem ray_tendsto_of_identity (P : PotPair → ℂ → ℂ)
    (hcont : ∀ ψ ∈ gkW, ∀ z : ℂ, z ∉ gapSegments38 ψ → ContinuousAt (Function.uncurry P) (ψ, z))
    (hid : ∀ ψ ∈ gkW, ∀ z : ℂ, z ∉ gapSegments38 ψ →
      2 * Complex.cosh (P ψ z) = NlsGge.GK38.discrim ψ z)
    (hbound : ∀ (ψ : PotPair) (t : ℝ), ‖ψ.1‖ * ‖ψ.2‖ + 1 ≤ t →
      ‖(Real.exp (-t) : ℂ) * NlsGge.GK38.discrim ψ (Complex.I * t) - 1‖ ≤
        Real.exp (-(2 * t)) + ‖ψ.1‖ * ‖ψ.2‖ / (2 * t) + (‖ψ.1‖ * ‖ψ.2‖ / t) ^ 2)
    (hvac : ∀ t : ℝ, P 0 (Complex.I * t) = t)
    (φ : PotPair) (hφ : φ ∈ gkW) :
    Tendsto (fun t : ℝ => P φ (Complex.I * t) - t) atTop (𝓝 0) := by
  refine preconnected_propagate gkW isConnected_gkW38.isPreconnected
    (fun ψ => Tendsto (fun t : ℝ => P ψ (Complex.I * t) - t) atTop (𝓝 0)) ?_ 0 free_mem_gkW ?_ φ hφ
  · intro ψ₀ h₀
    obtain ⟨V, hV, hVW, B, hB⟩ := ray_cutFree_uniform ψ₀ h₀
    set W : Set PotPair := V ∩ ball ψ₀ 1 with hWdef
    have hW : W ∈ 𝓝 ψ₀ := inter_mem hV (ball_mem_nhds _ one_pos)
    set K : ℝ := (‖ψ₀‖ + 1) ^ 2 with hK
    set g : ℝ → ℝ := fun t => 3 * Real.exp (-(2 * t)) + K / (2 * t) + (K / t) ^ 2 with hgdef
    have hg : Tendsto g atTop (𝓝 0) := ray_gauge_tendsto K
    have he8 : ∀ᶠ t : ℝ in atTop, Real.exp (-(2 * t)) < 1 / 8 := by
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (two_pos : (0 : ℝ) < 2))).eventually
          (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
      exact h
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 ((eventually_ge_atTop (K + 1)).and
      ((eventually_gt_atTop B).and ((hg.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and he8)))
    have hK0 : 0 ≤ K := sq_nonneg _
    -- membership facts on the ray
    have hfib : ∀ ψ ∈ W, ∀ t : ℝ, T₀ ≤ t →
        ψ ∈ gkW ∧ Complex.I * (t : ℂ) ∉ gapSegments38 ψ :=
      fun ψ hψ t ht => ⟨hVW hψ.1, hB ψ hψ.1 t (hT₀ t ht).2.1⟩
    refine ray_tendsto_locally_constant (fun ψ t => P ψ (Complex.I * t) - t) ψ₀ W hW T₀ g hg
      ?_ ?_ ?_
    · intro ψ hψ t ht
      obtain ⟨htK, -, hgt, he⟩ := hT₀ t ht
      have ht0 : 0 < t := by linarith
      have hq := ray_quadratic _ _ t (hid ψ (hfib ψ hψ t ht).1 _ (hfib ψ hψ t ht).2)
      -- norm bounds
      have hψb : ‖ψ‖ ≤ ‖ψ₀‖ + 1 := by
        have h1 := hψ.2
        rw [mem_ball, dist_eq_norm] at h1
        linarith [norm_sub_norm_le ψ ψ₀]
      have hm0 : 0 ≤ ‖ψ.1‖ * ‖ψ.2‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hmK : ‖ψ.1‖ * ‖ψ.2‖ ≤ K := by
        rw [hK, sq]
        exact mul_le_mul ((norm_fst_le ψ).trans hψb) ((norm_snd_le ψ).trans hψb)
          (norm_nonneg _) (by positivity)
      have hray := hbound ψ t (by linarith)
      have hmono : Real.exp (-(2 * t)) + ‖ψ.1‖ * ‖ψ.2‖ / (2 * t) + (‖ψ.1‖ * ‖ψ.2‖ / t) ^ 2 ≤
          Real.exp (-(2 * t)) + K / (2 * t) + (K / t) ^ 2 := by
        have h2 : ‖ψ.1‖ * ‖ψ.2‖ / (2 * t) ≤ K / (2 * t) :=
          div_le_div_of_nonneg_right hmK (by positivity)
        have h3 : (‖ψ.1‖ * ‖ψ.2‖ / t) ^ 2 ≤ (K / t) ^ 2 :=
          pow_le_pow_left₀ (div_nonneg hm0 ht0.le) (div_le_div_of_nonneg_right hmK ht0.le) 2
        linarith
      have hexp0 : 0 ≤ Real.exp (-(2 * t)) := (Real.exp_pos _).le
      have hD : ‖((Real.exp (-t) : ℝ) : ℂ) * NlsGge.GK38.discrim ψ (Complex.I * t) - 1‖ ≤ 1 / 4 := by
        have : g t = 3 * Real.exp (-(2 * t)) + K / (2 * t) + (K / t) ^ 2 := rfl
        linarith
      rcases quad_dichotomy _ _ _ hq hD with hb | hs
      · left
        rw [norm_exp_neg_sq] at hb
        show ‖Complex.exp (P ψ (Complex.I * t) - t) - 1‖ ≤ g t
        have : g t = 3 * Real.exp (-(2 * t)) + K / (2 * t) + (K / t) ^ 2 := rfl
        linarith
      · right
        rw [norm_exp_neg_sq] at hs
        show ‖Complex.exp (P ψ (Complex.I * t) - t)‖ < 1 / 2
        linarith
    · intro ψ hψ t ht
      have hc := hcont ψ (hfib ψ hψ t ht).1 _ (hfib ψ hψ t ht).2
      have hcomp : ContinuousAt (fun s : ℝ => Function.uncurry P (ψ, Complex.I * (s : ℂ))) t :=
        ContinuousAt.comp_of_eq hc (by fun_prop) rfl
      exact (hcomp.sub Complex.continuous_ofReal.continuousAt).continuousWithinAt
    · intro t ht
      have hc := hcont ψ₀ (hfib ψ₀ (mem_of_mem_nhds hW) t ht).1 _ (hfib ψ₀ (mem_of_mem_nhds hW) t ht).2
      have hcomp : ContinuousAt (fun ψ : PotPair => Function.uncurry P (ψ, Complex.I * (t : ℂ))) ψ₀ :=
        ContinuousAt.comp_of_eq hc (by fun_prop) rfl
      exact hcomp.sub continuousAt_const
  · refine tendsto_const_nhds.congr fun t => ?_
    show (0 : ℂ) = P 0 (Complex.I * t) - t
    rw [hvac, sub_self]

end NlsGge.ThirdConsultation.M016ChartAux
