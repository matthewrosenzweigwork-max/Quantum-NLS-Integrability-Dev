import NlsGge.GK38.TauGammaExteriorFarBounds
import NlsGge.GK38.TauGammaExteriorEvaluations
import NlsGge.GK38.TauGammaCriticalTails
import NlsGge.GK38.TauGammaFiniteBounds

/-! Actual exterior critical errors have a common full-index local square bound. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem exterior_critical_common_l2_bound38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ gkW ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ φ ∈ V,
      Summable (fun n : ℤ => ‖exteriorFactor38 φ n (lamDot φ n) - 1‖ ^ 2) ∧
      Summable (fun n : ℤ => ‖deriv (exteriorFactor38 φ n) (lamDot φ n)‖ ^ 2) ∧
      (∑' n : ℤ, ‖exteriorFactor38 φ n (lamDot φ n) - 1‖ ^ 2) ≤ C ∧
      (∑' n : ℤ, ‖deriv (exteriorFactor38 φ n) (lamDot φ n)‖ ^ 2) ≤ C := by
  obtain ⟨UK, hUK, K, hK, hNorm⟩ := periodic_deviation_norms_local38 φ₀
  obtain ⟨B, hB, hPair⟩ := paired_omit_cauchy38 K hK
  obtain ⟨Ud, hUd, D, hD, hDev⟩ := critical_l2 φ₀
  obtain ⟨Ut, hUt, hUtW, N, hTail⟩ := critical_uniform_tail38 φ₀ hφ₀ (Real.pi / 8) (by positivity)
  obtain ⟨Ks, hKs, hSinc⟩ := sinc_square_inner_bound38
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  obtain ⟨Uv, hUv, Fv, hFv, hFiniteV⟩ := finite_continuous_seq_bound38
    (fun φ n => exteriorFactor38 φ n (lamDot φ n) - 1) S φ₀
    (fun n _ => ((exterior_critical_analytic38 n).sub analyticOnNhd_const φ₀ hφ₀).continuousAt)
  obtain ⟨Up, hUp, Fp, hFp, hFiniteP⟩ := finite_continuous_seq_bound38
    (fun φ n => deriv (exteriorFactor38 φ n) (lamDot φ n)) S φ₀
    (fun n _ => (exterior_deriv_critical_analytic38 n φ₀ hφ₀).continuousAt)
  let F := Fv + Fp
  have hF : 0 ≤ F := add_nonneg hFv hFp
  let V := Ut ∩ (UK ∩ (Ud ∩ (Uv ∩ Up)))
  have hV : V ∈ 𝓝 φ₀ := inter_mem hUt (inter_mem hUK (inter_mem hUd (inter_mem hUv hUp)))
  refine ⟨V, hV, fun φ hφ => hUtW hφ.1,
    (S.card : ℝ) * F ^ 2 + 2 * B + 2 * Ks ^ 2 * D, by positivity, ?_⟩
  intro φ hφ
  obtain ⟨b, hb, hbs, hbB⟩ := hPair (periodicPlusDeviation38 φ) (periodicMinusDeviation38 φ)
    (hNorm φ hφ.2.1).1 (hNorm φ hφ.2.1).2
  have hfar (n : ℤ) (hn : n ∉ S) :
      ‖exteriorFactor38 φ n (lamDot φ n) - 1‖ ≤ b n + Ks * ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ ∧
      ‖deriv (exteriorFactor38 φ n) (lamDot φ n)‖ ≤ b n + Ks * ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ := by
    have hnf : (N : ℤ) < |n| := by
      have hh : ¬ (-(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) := by simpa only [S, Finset.mem_Icc] using hn
      by_contra h
      exact hh (abs_le.mp (not_lt.mp h))
    have hsmall := hTail φ hφ.1 n hnf
    have hz : lamDot φ n ∈ ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 8) :=
      mem_ball_iff_norm.mpr hsmall
    have hzOuter : lamDot φ n ∈ ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) :=
      mem_ball_iff_norm.mpr (by linarith [Real.pi_pos])
    exact exterior_inner_error_bounds38 φ n (lamDot φ n) hz (b n) Ks
      ((hb n).2 (lamDot φ n) hz) (hSinc n (lamDot φ n) hzOuter)
  have hfv (n : ℤ) (hn : n ∈ S) : ‖exteriorFactor38 φ n (lamDot φ n) - 1‖ ≤ F := by
    exact (hFiniteV φ hφ.2.2.2.1 n hn).trans (le_add_of_nonneg_right hFp)
  have hfp (n : ℤ) (hn : n ∈ S) : ‖deriv (exteriorFactor38 φ n) (lamDot φ n)‖ ≤ F := by
    exact (hFiniteP φ hφ.2.2.2.2 n hn).trans (le_add_of_nonneg_left hFv)
  have hdev := hDev φ hφ.2.2.1
  have hv := finite_tail_square_sum38 (fun n => exteriorFactor38 φ n (lamDot φ n) - 1)
    S F Ks B D hF hKs.le b (fun n => ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖)
    (fun n => (hb n).1) (fun n => norm_nonneg _) hbs hdev.1 hbB hdev.2 hfv
    (fun n hn => (hfar n hn).1)
  have hp := finite_tail_square_sum38 (fun n => deriv (exteriorFactor38 φ n) (lamDot φ n))
    S F Ks B D hF hKs.le b (fun n => ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖)
    (fun n => (hb n).1) (fun n => norm_nonneg _) hbs hdev.1 hbB hdev.2 hfp
    (fun n hn => (hfar n hn).2)
  exact ⟨hv.1, hp.1, hv.2, hp.2⟩

theorem exterior_critical_l2_38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    IsLocUnifL2Seq (fun φ n => exteriorFactor38 φ n (lamDot φ n) - 1) φ₀ ∧
      IsLocUnifL2Seq (fun φ n => deriv (exteriorFactor38 φ n) (lamDot φ n)) φ₀ := by
  obtain ⟨V, hV, _, C, _, h⟩ := exterior_critical_common_l2_bound38 φ₀ hφ₀
  exact ⟨⟨V, hV, C, fun φ hφ => ⟨(h φ hφ).1, (h φ hφ).2.2.1⟩⟩,
    ⟨V, hV, C, fun φ hφ => ⟨(h φ hφ).2.1, (h φ hφ).2.2.2⟩⟩⟩

end
end NlsGge.GK38
