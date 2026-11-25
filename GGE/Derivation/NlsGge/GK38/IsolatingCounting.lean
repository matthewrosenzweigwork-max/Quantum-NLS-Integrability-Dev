import NlsGge.GK38.IsolatingCriticalAnalytic
import NlsGge.GK38.IsolatingDefs

/-! One directly certified prescribed cutoff for all four actual functions.
GK I.5/I.6 counting route; no upward validity assumption is used. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem common_counting_boundaries38 (φ₀ : PotPair) (L : ℕ) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, L ≤ N ∧ ∀ φ ∈ U,
      RootCountingAt38 (perChar φ) 2 N ∧ RootCountingAt38 (deriv (discrim φ)) 1 N ∧
      RootCountingAt38 (dirichletChar φ) 1 N ∧ RootCountingAt38 (neumannChar38 φ) 1 N ∧
      ∀ n : ℤ, (N : ℤ) < |n| → ∀ z ∈ sphere (countingCenter38 n) (Real.pi / 4),
        perChar φ z ≠ 0 ∧ deriv (discrim φ) z ≠ 0 ∧ dirichletChar φ z ≠ 0 ∧ neumannChar38 φ z ≠ 0 := by
  obtain ⟨U₁, hU₁, R₁, herr₁⟩ := perChar_asymp φ₀ 1 (by norm_num)
  obtain ⟨U₂, hU₂, R₂, herr₂⟩ := discrimDeriv_asymp φ₀ (1 / sineOffDiscsConstant38)
    (one_div_pos.mpr sineOffDiscsConstant38_pos)
  obtain ⟨U₃, hU₃, R₃, herr₃⟩ := dirichletChar_asymp φ₀ (1 / (2 * sineOffDiscsConstant38))
    (one_div_pos.mpr (mul_pos (by norm_num) sineOffDiscsConstant38_pos))
  obtain ⟨U₄, hU₄, R₄, herr₄⟩ := dirichletChar_asymp (-φ₀) (1 / (2 * sineOffDiscsConstant38))
    (one_div_pos.mpr (mul_pos (by norm_num) sineOffDiscsConstant38_pos))
  have hU₄' : (fun φ : PotPair => -φ) ⁻¹' U₄ ∈ 𝓝 φ₀ :=
    continuous_neg.continuousAt.preimage_mem_nhds hU₄
  let R : ℝ := max (max R₁ R₂) (max R₃ R₄)
  obtain ⟨K, hK⟩ := exists_nat_gt (R / Real.pi)
  let N : ℕ := max (K + 1) L
  have hN : 0 < N := lt_of_lt_of_le (Nat.succ_pos K) (le_max_left _ _)
  have hRN : R ≤ countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    have hKN : (K : ℝ) < (N : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (Nat.lt_succ_self K) (le_max_left _ _)
    unfold countingRadius38
    nlinarith [Real.pi_pos]
  have hR₁ : R₁ ≤ countingRadius38 N :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hRN
  have hR₂ : R₂ ≤ countingRadius38 N :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hRN
  have hR₃ : R₃ ≤ countingRadius38 N :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hRN
  have hR₄ : R₄ ≤ countingRadius38 N :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hRN
  refine ⟨(U₁ ∩ U₂) ∩ (U₃ ∩ ((fun φ : PotPair => -φ) ⁻¹' U₄)),
    inter_mem (inter_mem hU₁ hU₂) (inter_mem hU₃ hU₄'), N, le_max_right _ _, fun φ hφ => ?_⟩
  have hcmp₁ : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖perChar φ z - perChar 0 z‖ < ‖perChar 0 z‖ := by
    intro z hz hsep
    apply counting_strict_comparison38
    · simpa only [one_mul] using herr₁ φ hφ.1.1 z (hR₁.trans hz) hsep
    · exact hsep
  have hcmp₂ : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖deriv (discrim φ) z - deriv (discrim 0) z‖ < ‖deriv (discrim 0) z‖ := by
    intro z hz hsep
    exact critical_strict_comparison38 (herr₂ φ hφ.1.2 z (hR₂.trans hz)) hsep
  have hcmp₃ : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖dirichletChar φ z - dirichletChar 0 z‖ < ‖dirichletChar 0 z‖ := by
    intro z hz hsep
    exact dirichlet_strict_comparison38 (herr₃ φ hφ.2.1 z (hR₃.trans hz)) hsep
  have hcmp₄ : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖dirichletChar (-φ) z - dirichletChar 0 z‖ < ‖dirichletChar 0 z‖ := by
    intro z hz hsep
    exact dirichlet_strict_comparison38 (herr₄ (-φ) hφ.2.2 z (hR₄.trans hz)) hsep
  have hnorm : countingRadius38 N ≤ ‖(countingRadius38 N : ℂ)‖ := by
    simp [Complex.norm_real, abs_of_pos (countingRadius_pos38 N)]
  have hsep := counting_central_sphere_separated38 N (counting_radius_mem_sphere38 N)
  obtain ⟨hs₁, hc₁, he₁⟩ := periodic_counting_at38 φ N hcmp₁
  obtain ⟨hs₂, hc₂, he₂⟩ := critical_counting_at38 φ N hcmp₂
  have hp : RootCountingAt38 (perChar φ) 2 N := by
    refine ⟨hN, analyticOnNhd_perChar_z φ,
      ⟨_, counting_ne_zero_of_comparison38 (hcmp₁ _ hnorm hsep)⟩,
      counting_zeroMult_support_finite38 φ, hs₁, ?_, he₁⟩
    omega
  have hd : RootCountingAt38 (deriv (discrim φ)) 1 N :=
    ⟨hN, analyticOnNhd_discrimDeriv38 φ,
      ⟨_, critical_ne_zero_of_comparison38 (hcmp₂ _ hnorm hsep)⟩,
      critical_zeroMult_support_finite38 φ, hs₂, by simpa only [one_mul] using hc₂, he₂⟩
  refine ⟨hp, hd, dirichlet_counting_at38 φ N hN hcmp₃,
    (neumann_counting_iff38 φ N).mpr (dirichlet_counting_at38 (-φ) N hN hcmp₄), ?_⟩
  intro n hn z hz
  have hzn := counting_far_sphere_norm38 hn hz
  have hzs := counting_small_sphere_separated38 n hz
  refine ⟨counting_ne_zero_of_comparison38 (hcmp₁ z hzn hzs),
    critical_ne_zero_of_comparison38 (hcmp₂ z hzn hzs),
    dirichlet_ne_zero_of_comparison38 (hcmp₃ z hzn hzs), ?_⟩
  rw [neumannChar38_eq_dirichlet_neg]
  exact dirichlet_ne_zero_of_comparison38 (hcmp₄ z hzn hzs)

theorem prescribed_common_counting38 (φ₀ : PotPair) (L : ℕ) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, L ≤ N ∧ ∀ φ ∈ U,
      RootCountingAt38 (perChar φ) 2 N ∧ RootCountingAt38 (deriv (discrim φ)) 1 N ∧
      RootCountingAt38 (dirichletChar φ) 1 N ∧ RootCountingAt38 (neumannChar38 φ) 1 N := by
  obtain ⟨U, hU, N, hN, h⟩ := common_counting_boundaries38 φ₀ L
  exact ⟨U, hU, N, hN, fun φ hφ =>
    ⟨(h φ hφ).1, (h φ hφ).2.1, (h φ hφ).2.2.1, (h φ hφ).2.2.2.1⟩⟩

end
end NlsGge.GK38
