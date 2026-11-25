import NlsGge.GK38.TauGammaDenominator
import NlsGge.GK38.TauGammaExteriorTails
import NlsGge.GK38.TauGammaDeltaBounds

/-! A common positive denominator bound covers all complex indices, finite and far. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem critical_denominator_analytic38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (n : ℤ) :
    AnalyticOnNhd ℂ (fun φ => criticalDenominator38 C R φ n) gkW := by
  have hQ := exterior_critical_analytic38 n
  have hP := exterior_deriv_critical_analytic38 n
  have hδ := (lamDot_analytic38 n).sub (tauN_analytic38 C R hsel n)
  exact (analyticOnNhd_const.mul hQ).add (hδ.mul hP)

theorem critical_denominator_common_bound38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ gkW ∧ ∃ b : ℝ, 0 < b ∧
      ∀ φ ∈ V, ∀ n : ℤ, b ≤ ‖criticalDenominator38 C R φ n‖ := by
  obtain ⟨Ud, hUd, hUdW, K, hK, hDelta⟩ := critical_delta_local_bound38 C R hsel φ₀ hφ₀
  let ε := 1 / (4 * (K + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεEq : 4 * (K + 1) * ε = 1 := by dsimp [ε]; field_simp
  obtain ⟨Ut, hUt, _, N, hTail⟩ := exterior_uniform_tail38 φ₀ hφ₀ ε hε
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hpos (n : ℤ) (_hn : n ∈ S) : 0 < ‖criticalDenominator38 C R φ₀ n‖ / 2 :=
    half_pos (norm_pos_iff.mpr (critical_denominator_nonzero38 C R hsel φ₀ hφ₀ n))
  obtain ⟨b₀, hb₀, hbLower⟩ := isolating_finite_pos_lower38 S
    (fun n => ‖criticalDenominator38 C R φ₀ n‖ / 2) hpos
  have hfinite : ∀ᶠ φ in 𝓝 φ₀, ∀ n ∈ S,
      ‖criticalDenominator38 C R φ₀ n‖ / 2 < ‖criticalDenominator38 C R φ n‖ := by
    apply (Filter.eventually_all_finset S).mpr
    intro n hn
    exact (critical_denominator_analytic38 C R hsel n φ₀ hφ₀).continuousAt.norm.eventually
      (lt_mem_nhds (half_lt_self (norm_pos_iff.mpr (critical_denominator_nonzero38 C R hsel φ₀ hφ₀ n))))
  let Uf : Set PotPair := {φ | ∀ n ∈ S,
    ‖criticalDenominator38 C R φ₀ n‖ / 2 < ‖criticalDenominator38 C R φ n‖}
  have hUf : Uf ∈ 𝓝 φ₀ := Filter.eventually_iff.mp hfinite
  refine ⟨Ud ∩ (Ut ∩ Uf), inter_mem hUd (inter_mem hUt hUf), fun φ hφ => hUdW hφ.1,
    min b₀ 1, lt_min hb₀ (by norm_num), fun φ hφ n => ?_⟩
  by_cases hn : n ∈ S
  · exact (min_le_left b₀ 1).trans ((hbLower n hn).trans (hφ.2.2 n hn).le)
  · have hnf : (N : ℤ) < |n| := by
      have hh : ¬ (-(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) := by simpa only [S, Finset.mem_Icc] using hn
      by_contra h
      exact hh (abs_le.mp (not_lt.mp h))
    obtain ⟨hQ, hP⟩ := hTail φ hφ.2.1 n hnf
    have hδ := hDelta φ hφ.1 n
    have he : criticalDenominator38 C R φ n - 2 =
        2 * (exteriorFactor38 φ n (lamDot φ n) - 1) +
          (lamDot φ n - tauN38 C R φ n) * deriv (exteriorFactor38 φ n) (lamDot φ n) := by
      unfold criticalDenominator38
      ring
    have herror : ‖criticalDenominator38 C R φ n - 2‖ ≤ 2 * ε + K * ε := by
      rw [he]
      calc
        _ ≤ ‖2 * (exteriorFactor38 φ n (lamDot φ n) - 1)‖ +
            ‖(lamDot φ n - tauN38 C R φ n) * deriv (exteriorFactor38 φ n) (lamDot φ n)‖ := norm_add_le _ _
        _ = 2 * ‖exteriorFactor38 φ n (lamDot φ n) - 1‖ +
            ‖lamDot φ n - tauN38 C R φ n‖ * ‖deriv (exteriorFactor38 φ n) (lamDot φ n)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hQ.le (by norm_num))
          (mul_le_mul hδ hP.le (norm_nonneg _) hK)
    have hunit : 2 * ε + K * ε ≤ 1 := by nlinarith [mul_nonneg hK hε.le]
    have ht := norm_le_norm_sub_add (2 : ℂ) (criticalDenominator38 C R φ n)
    rw [Complex.norm_ofNat, norm_sub_rev] at ht
    have hlower : 1 ≤ ‖criticalDenominator38 C R φ n‖ := by linarith
    exact (min_le_right b₀ 1).trans hlower

end
end NlsGge.GK38
