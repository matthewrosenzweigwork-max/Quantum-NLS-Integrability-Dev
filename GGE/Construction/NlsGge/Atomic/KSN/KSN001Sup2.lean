import Mathlib
import NlsGge.GK38.Defs
import NlsGge.ThirdConsultation.G5.G5017Support1

                                                                                                                                   
                                                    
                                                                                                                      
                                                                                                                       
                                                                                     
                                                                                                                 
                                                                                                                         
                                                                                                                     
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.G5017Support1

namespace NlsGge.ThirdConsultation.KSN
namespace KSN001Aux
noncomputable section

/-- Every pair is a real-slice point plus `I` times a real-slice point, with norm control. -/
theorem realSlice_decomp (ψ : PotPair) :
    ∃ u v : PhysicalL2, ψ = realSlice u + Complex.I • realSlice v ∧ ‖u‖ ≤ ‖ψ‖ ∧ ‖v‖ ≤ ‖ψ‖ := by
  have hns : ∀ y : PhysicalL2, ‖star y‖ = ‖y‖ := fun y => starLp.norm_map y
  have h1 : ‖ψ.1‖ ≤ ‖ψ‖ := norm_fst_le ψ
  have h2 : ‖ψ.2‖ ≤ ‖ψ‖ := norm_snd_le ψ
  have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hhi : ‖(Complex.I / 2 : ℂ)‖ = 1 / 2 := by simp
  have hhn : ‖(-Complex.I / 2 : ℂ)‖ = 1 / 2 := by simp
  refine ⟨(1 / 2 : ℂ) • ψ.1 + (1 / 2 : ℂ) • star ψ.2,
    (-Complex.I / 2 : ℂ) • ψ.1 + (Complex.I / 2 : ℂ) • star ψ.2, ?_, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, realSlice_fst]
      rw [smul_add, smul_smul, smul_smul]
      have e1 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
        rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; norm_num
      have e2 : Complex.I * (Complex.I / 2) = -(1 / 2) := by
        rw [mul_div_assoc', Complex.I_mul_I]; norm_num
      rw [e1, e2]
      module
    · simp only [Prod.snd_add, Prod.smul_snd, realSlice_snd]
      rw [star_add_lp, star_add_lp, star_smul_lp, star_smul_lp, star_smul_lp, star_smul_lp, star_star,
        smul_add, smul_smul, smul_smul]
      have c2' : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
      have c1 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
        rw [map_div₀, map_one, c2']
      have c2 : (starRingEnd ℂ) (-Complex.I / 2 : ℂ) = Complex.I / 2 := by
        rw [map_div₀, map_neg, Complex.conj_I, neg_neg, c2']
      have c3 : (starRingEnd ℂ) (Complex.I / 2 : ℂ) = -Complex.I / 2 := by
        rw [map_div₀, Complex.conj_I, c2']
      rw [c1, c2, c3]
      have e1 : Complex.I * (Complex.I / 2) = -(1 / 2) := by
        rw [mul_div_assoc', Complex.I_mul_I]; norm_num
      have e2 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
        rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; norm_num
      rw [e1, e2]
      module
  · calc ‖(1 / 2 : ℂ) • ψ.1 + (1 / 2 : ℂ) • star ψ.2‖
        ≤ ‖(1 / 2 : ℂ) • ψ.1‖ + ‖(1 / 2 : ℂ) • star ψ.2‖ := norm_add_le _ _
      _ = 1 / 2 * ‖ψ.1‖ + 1 / 2 * ‖ψ.2‖ := by rw [norm_smul, norm_smul, hh, hns]
      _ ≤ ‖ψ‖ := by linarith
  · calc ‖(-Complex.I / 2 : ℂ) • ψ.1 + (Complex.I / 2 : ℂ) • star ψ.2‖
        ≤ ‖(-Complex.I / 2 : ℂ) • ψ.1‖ + ‖(Complex.I / 2 : ℂ) • star ψ.2‖ := norm_add_le _ _
      _ = 1 / 2 * ‖ψ.1‖ + 1 / 2 * ‖ψ.2‖ := by rw [norm_smul, norm_smul, hhn, hhi, hns]
      _ ≤ ‖ψ‖ := by linarith

/-- Real points of the real slice: `realSlice` is real-linear and `(x : ℂ) • _ = x • _`. -/
theorem realSlice_line (u₀ u v : PhysicalL2) (x : ℝ) :
    realSlice u₀ + realSlice u + (x : ℂ) • realSlice v = realSlice (u₀ + u + x • v) := by
  rw [map_add, map_add, map_smul]
  congr 1

/-- The real line accumulates at `0` in the punctured complex neighbourhood. -/
theorem ofReal_tendsto_nhdsNE :
    Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx

/-- Local step: an analytic function vanishing on the real slice vanishes near every real point of an open set. -/
theorem eventually_zero_of_realSlice (S : Set PotPair) (hS : IsOpen S)
    (f : PotPair → ℂ) (hf : AnalyticOnNhd ℂ f S) (u₀ : PhysicalL2) (hu₀ : realSlice u₀ ∈ S)
    (hr : ∀ u : PhysicalL2, realSlice u ∈ S → f (realSlice u) = 0) :
    f =ᶠ[𝓝 (realSlice u₀)] 0 := by
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.1 hS _ hu₀
  have hmem : Metric.ball (realSlice u₀) (r / 3) ∈ 𝓝 (realSlice u₀) :=
    Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hmem] with φ hφ
  show f φ = 0
  obtain ⟨u, v, hdec, hu, hv⟩ := realSlice_decomp (φ - realSlice u₀)
  have hd : ‖φ - realSlice u₀‖ < r / 3 := by rwa [Metric.mem_ball, dist_eq_norm] at hφ
  have hpt : ∀ t : ℂ, ‖t‖ < 2 → realSlice u₀ + realSlice u + t • realSlice v ∈ S := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have e : realSlice u₀ + realSlice u + t • realSlice v - realSlice u₀ = realSlice u + t • realSlice v := by
      abel
    rw [e]
    have htv : ‖t‖ * ‖v‖ ≤ 2 * ‖φ - realSlice u₀‖ := by
      nlinarith [norm_nonneg t, norm_nonneg v]
    calc ‖realSlice u + t • realSlice v‖ ≤ ‖realSlice u‖ + ‖t • realSlice v‖ := norm_add_le _ _
      _ = ‖u‖ + ‖t‖ * ‖v‖ := by rw [norm_smul, norm_realSlice, norm_realSlice]
      _ < r := by linarith
  have hga : AnalyticOnNhd ℂ (fun t : ℂ => f (realSlice u₀ + realSlice u + t • realSlice v))
      (Metric.ball (0 : ℂ) 2) := by
    intro t ht
    have hin : realSlice u₀ + realSlice u + t • realSlice v ∈ S := hpt t (by simpa using ht)
    have hlin : AnalyticAt ℂ (fun s : ℂ => realSlice u₀ + realSlice u + s • realSlice v) t :=
      by fun_prop
    exact (hf (realSlice u₀ + realSlice u + t • realSlice v) hin).comp
      (f := fun s : ℂ => realSlice u₀ + realSlice u + s • realSlice v) hlin
  have hreal : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ),
      f (realSlice u₀ + realSlice u + (x : ℂ) • realSlice v) = 0 := by
    have hn : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), ‖(x : ℂ)‖ < 2 := by
      have hc : Tendsto (fun x : ℝ => ‖(x : ℂ)‖) (𝓝 0) (𝓝 0) := by
        have := (Complex.continuous_ofReal.norm.tendsto (0 : ℝ))
        simpa using this
      exact hc.eventually (gt_mem_nhds (by norm_num))
    filter_upwards [nhdsWithin_le_nhds hn] with x hx
    have hin := hpt (x : ℂ) hx
    rw [realSlice_line] at hin ⊢
    exact hr _ hin
  have hfreq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), f (realSlice u₀ + realSlice u + t • realSlice v) = 0 :=
    ofReal_tendsto_nhdsNE.frequently
      (p := fun t : ℂ => f (realSlice u₀ + realSlice u + t • realSlice v) = 0) hreal.frequently
  have hEq := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball (0 : ℂ) 2).isPreconnected
    (Metric.mem_ball_self (by norm_num)) hfreq
  have hI : Complex.I ∈ Metric.ball (0 : ℂ) 2 := by
    rw [mem_ball_zero_iff, Complex.norm_I]; norm_num
  have h := hEq hI
  have hpt' : realSlice u₀ + realSlice u + Complex.I • realSlice v = φ := by
    rw [add_assoc, ← hdec]
    abel
  simp only [Pi.zero_apply] at h
  rw [hpt'] at h
  exact h

/-- (M2) of KSN001_STOP.md: identity theorem from the totally real slice. -/
theorem analyticOnNhd_eq_zero_of_realSlice (S : Set PotPair) (hS : IsOpen S) (hc : IsPreconnected S)
    (f : PotPair → ℂ) (hf : AnalyticOnNhd ℂ f S) (u₀ : PhysicalL2) (hu₀ : realSlice u₀ ∈ S)
    (hr : ∀ u : PhysicalL2, realSlice u ∈ S → f (realSlice u) = 0) :
  ∀ φ ∈ S, f φ = 0 := by
  intro φ hφ
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hu₀
    (eventually_zero_of_realSlice S hS f hf u₀ hu₀ hr) hφ

end
end KSN001Aux
end NlsGge.ThirdConsultation.KSN
