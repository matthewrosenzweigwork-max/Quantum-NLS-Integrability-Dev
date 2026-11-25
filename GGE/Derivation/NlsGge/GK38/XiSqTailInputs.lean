import NlsGge.GK38.XiSqCandidates
import NlsGge.GK38.TauGammaL2Realization

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

theorem a5Gamma2_l2_38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    IsLocUnifL2Seq (fun φ n => gamma2 φ n) φ₀ := by
  obtain ⟨V, hV, _hVW, B, hB, h⟩ := tauGamma_common_value_bound38 discC discR
    isolating_selectors_admissible38 φ₀ hφ₀
  refine ⟨V, hV, B^2, fun φ hφ => ?_⟩
  have hs : Summable (fun n : ℤ => ‖gamma2 φ n‖) := (h φ hφ).2.2.1
  have hmass : (∑' n : ℤ, ‖gamma2 φ n‖) ≤ B := (h φ hφ).2.2.2.2.2
  have hterm (n : ℤ) : ‖gamma2 φ n‖ ≤ B := by
    have hp := hs.sum_le_tsum ({n} : Finset ℤ) (fun _ _ => norm_nonneg _)
    have hp' : ‖gamma2 φ n‖ ≤ ∑' k : ℤ, ‖gamma2 φ k‖ := by
      simpa only [Finset.sum_singleton] using hp
    exact hp'.trans hmass
  have hdom := hs.mul_left B
  have hsq (n : ℤ) : ‖gamma2 φ n‖^2 ≤ B * ‖gamma2 φ n‖ := by
    nlinarith [norm_nonneg (gamma2 φ n), hterm n]
  have hss := hdom.of_nonneg_of_le (fun n => sq_nonneg _) hsq
  refine ⟨hss, (hss.tsum_le_tsum hsq hdom).trans ?_⟩
  rw [tsum_mul_left]
  nlinarith [mul_le_mul_of_nonneg_left hmass hB]

theorem a5Gamma2_l2_realization38 :
    ∃ A : PotPair → Lib.L2Z,
      (∀ φ ∈ gkW, ∀ n : ℤ, A φ n = gamma2 φ n) ∧
      AnalyticOnNhd ℂ A gkW :=
  local_l2_analytic_realization38 gkW (fun φ n => gamma2 φ n) isOpen_gkW
    gamma2_analytic a5Gamma2_l2_38

theorem a5Gamma2_uniform_tail38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ gkW ∧ ∃ N : ℕ,
      ∀ φ ∈ V, ∀ n : ℤ, (N : ℤ) < |n| → ‖gamma2 φ n‖ < ε := by
  obtain ⟨A, he, ha⟩ := a5Gamma2_l2_realization38
  obtain ⟨V, hV, N, ht⟩ := l2_continuous_local_tails38 A φ₀ (ha φ₀ hφ₀).continuousAt ε hε
  refine ⟨V ∩ gkW, inter_mem hV (isOpen_gkW.mem_nhds hφ₀), inter_subset_right, N, ?_⟩
  intro φ hφ n hn
  rw [← he φ hφ.2 n]
  exact ht φ hφ.1 n hn

/-- Honest conditional Hilbert realization; the normalized-error L2 estimate remains an input. -/
theorem a5XiSqError_l2_realization38 (g : ℤ → PotPair → ℂ)
    (hspec : ∀ n, XiSqSpec38 n (g n))
    (hl2 : ∀ φ₀ ∈ gkW, IsLocUnifL2Seq (fun φ n => g n φ - 1) φ₀) :
    ∃ A : PotPair → Lib.L2Z,
      (∀ φ ∈ gkW, ∀ n : ℤ, A φ n = g n φ - 1) ∧
      AnalyticOnNhd ℂ A gkW :=
  local_l2_analytic_realization38 gkW (fun φ n => g n φ - 1) isOpen_gkW
    (fun n => (hspec n).1.sub analyticOnNhd_const) hl2

theorem a5XiSq_near_one_of_l2_38 (g : ℤ → PotPair → ℂ)
    (hspec : ∀ n, XiSqSpec38 n (g n))
    (hl2 : ∀ φ₀ ∈ gkW, IsLocUnifL2Seq (fun φ n => g n φ - 1) φ₀)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ N : ℕ,
      ∀ φ ∈ U, ∀ n : ℤ, N < n.natAbs →
        g n φ ∈ Complex.slitPlane ∧ ‖g n φ - 1‖ < (1/2:ℝ) := by
  obtain ⟨A, he, ha⟩ := a5XiSqError_l2_realization38 g hspec hl2
  obtain ⟨V, hV, N, ht⟩ := l2_continuous_local_tails38 A φ₀
    (ha φ₀ hφ₀).continuousAt (1/2) (by norm_num)
  refine ⟨V ∩ gkW, inter_mem hV (isOpen_gkW.mem_nhds hφ₀), inter_subset_right, N, ?_⟩
  intro φ hφ n hn
  have hn' : (N : ℤ) < |n| := by
    have hc : (N : ℤ) < (n.natAbs : ℤ) := by exact_mod_cast hn
    simpa only [Int.natCast_natAbs] using hc
  have hsmall : ‖g n φ - 1‖ < (1/2:ℝ) := by
    rw [← he φ hφ.2 n]
    exact ht φ hφ.1 n hn'
  refine ⟨?_, hsmall⟩
  have hslit := Complex.mem_slitPlane_of_norm_lt_one
    (z := g n φ - 1) (by linarith : ‖g n φ - 1‖ < 1)
  have hid : (1 : ℂ) + (g n φ - 1) = g n φ := by ring
  rwa [hid] at hslit

/-- No slit-plane assumption or finite-head continuity hypothesis is needed here. -/
theorem a5XiSqrt_l2_of_l2_38 (g : ℤ → PotPair → ℂ) (φ₀ : PotPair)
    (hl2 : IsLocUnifL2Seq (fun φ n => g n φ - 1) φ₀) :
    IsLocUnifL2Seq (fun φ n => Complex.sqrt (g n φ) - 1) φ₀ := by
  apply hl2.mono
  filter_upwards [] with φ
  intro n
  have h := Lib.norm_sqrt_one_sub_sub_one_le (1 - g n φ)
  have hid : (1 : ℂ) - (1 - g n φ) = g n φ := by ring
  rw [hid, norm_sub_rev (1 : ℂ)] at h
  exact h

end
end NlsGge.GK38
