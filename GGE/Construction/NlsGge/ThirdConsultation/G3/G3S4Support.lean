import Mathlib
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G3.G3019
import NlsGge.Atomic.G3.G3RatioHost
import NlsGge.Atomic.G3.G3ZetaHost
import NlsGge.Atomic.G3.G3SegmentHost
import NlsGge.ThirdConsultation.G3.G3M12Support
import NlsGge.ThirdConsultation.G3.G3S1Support
import NlsGge.ThirdConsultation.G3.G3S23Support

                                                                                                          
                                                                                                           
                                                                                                                       
                                                                                                                
                                                                                                                        
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Pure algebra for the uniform estimate of R*G*omega against G0*omega0. -/
theorem g3s4_bound (R G G0 ω ω0 : ℂ) (δ M C1 W : ℝ) (hδ : 0 ≤ δ) (hR : ‖R - 1‖ ≤ δ)
    (hG : ‖G‖ ≤ M) (hGG0 : ‖G - G0‖ ≤ δ) (hG0 : ‖G0‖ ≤ C1) (hω : ‖ω‖ ≤ W)
    (hωω0 : ‖ω - ω0‖ ≤ δ) (hM : 0 ≤ M) (hW : 0 ≤ W) (hC1 : 0 ≤ C1) :
    ‖R * G * ω - G0 * ω0‖ ≤ δ * (M * W + W + C1) := by
  have hid : R * G * ω - G0 * ω0 = (R - 1) * G * ω + (G - G0) * ω + G0 * (ω - ω0) := by ring
  have h1 : ‖(R - 1) * G * ω‖ ≤ δ * M * W := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul hR hG (norm_nonneg _) hδ) hω (norm_nonneg _) (mul_nonneg hδ hM)
  have h2 : ‖(G - G0) * ω‖ ≤ δ * W := by
    rw [norm_mul]
    exact mul_le_mul hGG0 hω (norm_nonneg _) hδ
  have h3 : ‖G0 * (ω - ω0)‖ ≤ C1 * δ := by
    rw [norm_mul]
    exact mul_le_mul hG0 hωω0 (norm_nonneg _) hC1
  have hsum1 := norm_add_le ((R - 1) * G * ω) ((G - G0) * ω)
  have hsum2 := norm_add_le ((R - 1) * G * ω + (G - G0) * ω) (G0 * (ω - ω0))
  have hfin : δ * M * W + δ * W + C1 * δ = δ * (M * W + W + C1) := by ring
  rw [hid]
  linarith

theorem g3s4_final_tendsto (n m : ℤ) (hmn : m ≠ n) (v : ℕ → PotPair) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0))
    (hvmem : ∀ j, v j ∈ sourceW) (hnot : φ0 ∉ endpointSet m) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun j : ℕ => betaFinalSegment n m (v j) ε) atTop
      (𝓝 (collapsedBetaFinalSegment n m φ0 ε)) := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  have hlam := g3s1_lam_eq φ0 hgk0 m hgap
  have hunif := G3M2_betaZeta_unif n m hmn v φ0 hφ0 hgap hv ε hε
  have hωT := g3s1_omega_tendsto v φ0 m hφ0 hgap hv
  have hωlim : muSeq φ0 m - lamMinus φ0 m = muSeq φ0 m - tauN φ0 m := by rw [hlam.2]
  rw [hωlim] at hωT
  obtain ⟨U, hUo, hφ0U, hUgk, Cr, Rr, c, N, hg, hspecU⟩ := g2019_leaf_family φ0 hgk0
  have hG0c : ContinuousOn (fun t : ℝ => betaZeta n m φ0
      (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m))) (Icc ε 1) := by
    have h := g3s2_betaZeta_contOn n m hmn Cr Rr c N hg φ0 hgk0 (hspecU φ0 hφ0U) ε hε.1
    have hfun : (fun t : ℝ => betaZeta n m φ0
        (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m))) =
        fun t : ℝ => betaZeta n m φ0 (betaSegmentPoint m φ0 t) := by
      funext t
      rw [g3s1_seg_eq φ0 m hlam.2 t]
    rw [hfun]
    exact h
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := ε) (b := 1)).exists_bound_of_continuousOn hG0c
  obtain ⟨C1, hC1pos, hC1⟩ : ∃ C1 : ℝ, 0 < C1 ∧ ∀ t ∈ Icc ε 1,
      ‖betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m))‖ ≤ C1 :=
    ⟨max C0 0 + 1, by linarith [le_max_right C0 0],
      fun t ht => le_trans (hC0 t ht) (by linarith [le_max_left C0 0])⟩
  have hF : IntervalIntegrable (fun t : ℝ => betaZeta n m φ0
      (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)) volume ε 1 :=
    g3s3_integrable n m hmn φ0 hφ0 hgap hnot ε hε
  have hE := g3s2_eventually_integrable n m hmn v φ0 hφ0 hgap hv hvmem hnot ε hε
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (C1 + 1) * (‖muSeq φ0 m - tauN φ0 m‖ + 1) +
      (‖muSeq φ0 m - tauN φ0 m‖ + 1) + C1 := ⟨_, rfl⟩
  have hQpos : 0 ≤ Q := by
    rw [hQ]
    have := norm_nonneg (muSeq φ0 m - tauN φ0 m)
    nlinarith
  have hQ1 : Q + 1 ≠ 0 := ne_of_gt (by linarith)
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ1, hδ2, hδpos⟩ : ∃ δ : ℝ, δ ≤ 1 ∧ δ ≤ η / (2 * (Q + 1)) ∧ 0 < δ :=
    ⟨min 1 (η / (2 * (Q + 1))), min_le_left _ _, min_le_right _ _,
      lt_min one_pos (div_pos hη (by linarith))⟩
  have hδQ : δ * Q ≤ η / 2 := by
    have h1 : δ * (Q + 1) ≤ η / (2 * (Q + 1)) * (Q + 1) :=
      mul_le_mul_of_nonneg_right hδ2 (by linarith)
    have h2 : η / (2 * (Q + 1)) * (Q + 1) = η / 2 := by
      rw [div_mul_eq_mul_div, mul_div_mul_right η 2 hQ1]
    have h3 : δ * (Q + 1) = δ * Q + δ := by ring
    linarith
  have hA : ∀ᶠ j in atTop, ∀ t ∈ Icc ε 1,
      ‖betaRootRatioAlong n m (v j) t - 1‖ < δ := by
    obtain ⟨J, hJ⟩ := g3s1_conj1 n m hmn v φ0 hφ0 hgap hv hnot ε hε δ hδpos
    exact eventually_atTop.2 ⟨J, fun j hj t ht => (hJ j hj t ht).2⟩
  have hB : ∀ᶠ j in atTop, ∀ t ∈ Icc ε 1, dist
      (betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)))
      (betaZeta n m (v j) (betaSegmentPoint m (v j) t)) < δ :=
    Metric.tendstoUniformlyOn_iff.1 hunif δ hδpos
  have hC : ∀ᶠ j in atTop, dist (betaOmega m (v j)) (muSeq φ0 m - tauN φ0 m) < δ :=
    Metric.tendsto_nhds.1 hωT δ hδpos
  have hmain : ∀ᶠ j in atTop, ∀ t ∈ Icc ε 1,
      ‖betaSegmentDensity n m (v j) t - betaZeta n m φ0
        (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)‖ ≤ η / 2 := by
    filter_upwards [hA, hB, hC] with j hAj hBj hCj t ht
    have hR : ‖betaRootRatioAlong n m (v j) t - 1‖ ≤ δ := (hAj t ht).le
    have hdist : ‖betaZeta n m (v j) (betaSegmentPoint m (v j) t) -
        betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m))‖ < δ := by
      have h := hBj t ht
      rw [dist_comm, dist_eq_norm] at h
      exact h
    have hωd : ‖betaOmega m (v j) - (muSeq φ0 m - tauN φ0 m)‖ < δ := by
      rw [dist_eq_norm] at hCj
      exact hCj
    have hGj : ‖betaZeta n m (v j) (betaSegmentPoint m (v j) t)‖ ≤ C1 + 1 := by
      have h1 := norm_sub_norm_le (betaZeta n m (v j) (betaSegmentPoint m (v j) t))
        (betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)))
      have h0 := hC1 t ht
      linarith
    have hωW : ‖betaOmega m (v j)‖ ≤ ‖muSeq φ0 m - tauN φ0 m‖ + 1 := by
      have h1 := norm_sub_norm_le (betaOmega m (v j)) (muSeq φ0 m - tauN φ0 m)
      linarith
    have key := g3s4_bound (betaRootRatioAlong n m (v j) t)
      (betaZeta n m (v j) (betaSegmentPoint m (v j) t))
      (betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)))
      (betaOmega m (v j)) (muSeq φ0 m - tauN φ0 m) δ (C1 + 1) C1
      (‖muSeq φ0 m - tauN φ0 m‖ + 1) hδpos.le hR hGj hdist.le (hC1 t ht) hωW hωd.le
      (by linarith) (by positivity) hC1pos.le
    unfold betaSegmentDensity
    have hsub : δ * ((C1 + 1) * (‖muSeq φ0 m - tauN φ0 m‖ + 1) +
        (‖muSeq φ0 m - tauN φ0 m‖ + 1) + C1) = δ * Q := by rw [hQ]
    linarith
  filter_upwards [hE, hmain] with j hEj hmj
  rw [dist_eq_norm]
  unfold betaFinalSegment collapsedBetaFinalSegment
  rw [← intervalIntegral.integral_sub hEj hF]
  have hsub : Set.uIoc ε 1 ⊆ Icc ε 1 := by
    rw [uIoc_of_le hε.2.le]
    exact Ioc_subset_Icc_self
  have hbound : ‖∫ t in ε..1, (betaSegmentDensity n m (v j) t - betaZeta n m φ0
      (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m))‖ ≤
      η / 2 * |1 - ε| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => hmj t (hsub ht))
  have habs : |1 - ε| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hε.1, hε.2]
  have h4 : η / 2 * |1 - ε| ≤ η / 2 * 1 := mul_le_mul_of_nonneg_left habs (by linarith)
  exact lt_of_le_of_lt (le_trans hbound h4) (by linarith)

end
end NlsGge.GKDefinitionDesign
