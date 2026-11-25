import NlsGge.GK38.PeriodicLabellingDefs

/-! # S2: common certified cutoff for periodic and critical roots -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem periodic_counting_at38 (φ : PotPair) (N : ℕ)
    (hcmp : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖perChar φ z - perChar 0 z‖ < ‖perChar 0 z‖) :
    (∀ n : ℤ, (N : ℤ) < |n| →
      Multiset.card (Lib.zeroMultiset (perChar φ)
        (ball (countingCenter38 n) (Real.pi / 4))) = 2) ∧
    Multiset.card (Lib.zeroMultiset (perChar φ)
      (ball (0 : ℂ) (countingRadius38 N))) = 4 * N + 2 ∧
    ∀ z : ℂ, perChar φ z = 0 →
      z ∈ ball (0 : ℂ) (countingRadius38 N) ∨
        ∃ n : ℤ, (N : ℤ) < |n| ∧ z ∈ ball (countingCenter38 n) (Real.pi / 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    change Multiset.card (Lib.zeroMultiset (perChar φ)
      (ball (countingCenter38 n) (Real.pi / 4))) = 2
    have hfin := counting_zeroMult_support_finite38 φ (countingCenter38 n) (Real.pi / 4)
    refine Eq.trans ?_ (counting_free_small_card38 n)
    refine Lib.rouche_circle (by positivity : 0 < Real.pi / 4)
      ((analyticOnNhd_perChar_z 0).mono (subset_univ _))
      ((analyticOnNhd_perChar_z φ).mono (subset_univ _)) fun z hz => ?_
    exact hcmp z (counting_far_sphere_norm38 hn hz)
      (counting_small_sphere_separated38 n hz)
  · change Multiset.card (Lib.zeroMultiset (perChar φ)
      (ball (0 : ℂ) (countingRadius38 N))) = 4 * N + 2
    have hfin := counting_zeroMult_support_finite38 φ 0 (countingRadius38 N)
    refine Eq.trans ?_ (counting_free_central_card38 N)
    refine Lib.rouche_circle (countingRadius_pos38 N)
      ((analyticOnNhd_perChar_z 0).mono (subset_univ _))
      ((analyticOnNhd_perChar_z φ).mono (subset_univ _)) fun z hz => ?_
    have hz' : countingRadius38 N ≤ ‖z‖ := by
      have he : ‖z‖ = countingRadius38 N := by
        simpa only [mem_sphere, dist_zero_right] using hz
      exact he.ge
    exact hcmp z hz' (counting_central_sphere_separated38 N hz)
  · intro z hz0
    change z ∈ ball (0 : ℂ) (countingRadius38 N) ∨
      ∃ n : ℤ, (N : ℤ) < |n| ∧ z ∈ ball (countingCenter38 n) (Real.pi / 4)
    by_cases hz : z ∈ ball (0 : ℂ) (countingRadius38 N)
    · exact Or.inl hz
    · right
      by_contra h
      have hz' : countingRadius38 N ≤ ‖z‖ := by
        simpa only [mem_ball, dist_zero_right, not_lt] using hz
      have hfar : ∀ n : ℤ, (N : ℤ) < |n| → Real.pi / 4 ≤ ‖z - countingCenter38 n‖ := by
        intro n hn
        by_contra hs
        exact h ⟨n, hn, mem_ball_iff_norm.mpr (not_le.mp hs)⟩
      exact counting_ne_zero_of_comparison38
        (hcmp z hz' (counting_outside_separated38 N hz' hfar)) hz0


/-- The positive real endpoint belongs to the central circle. -/
theorem counting_radius_mem_sphere38 (N : ℕ) :
    (countingRadius38 N : ℂ) ∈ sphere (0 : ℂ) (countingRadius38 N) := by
  simp only [mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (countingRadius_pos38 N)]

theorem simultaneous_counting_lemma38 (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ,
      ∀ φ : PotPair, φ ∈ U →
        RootCountingAt38 (perChar φ) 2 N ∧ RootCountingAt38 (deriv (discrim φ)) 1 N := by
  obtain ⟨U₁, hU₁, R₁, herr₁⟩ := perChar_asymp φ₀ 1 (by norm_num)
  obtain ⟨U₂, hU₂, R₂, herr₂⟩ := discrimDeriv_asymp φ₀ (1 / sineOffDiscsConstant38)
    (one_div_pos.mpr sineOffDiscsConstant38_pos)
  obtain ⟨K, hK⟩ := exists_nat_gt (max R₁ R₂ / Real.pi)
  let N : ℕ := K + 1
  have hN : 0 < N := Nat.succ_pos K
  have hRN : max R₁ R₂ ≤ countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    unfold countingRadius38 N
    push_cast
    linarith [Real.pi_pos]
  refine ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, N, fun φ hφ => ?_⟩
  have hcmp₁ : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖perChar φ z - perChar 0 z‖ < ‖perChar 0 z‖ := by
    intro z hz hsep
    apply counting_strict_comparison38
    · simpa only [one_mul] using herr₁ φ hφ.1 z ((le_max_left _ _).trans (hRN.trans hz)) hsep
    · exact hsep
  have hcmp₂ : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖deriv (discrim φ) z - deriv (discrim 0) z‖ < ‖deriv (discrim 0) z‖ := by
    intro z hz hsep
    exact critical_strict_comparison38
      (herr₂ φ hφ.2 z ((le_max_right _ _).trans (hRN.trans hz))) hsep
  have hsphere := counting_radius_mem_sphere38 N
  have hnorm : countingRadius38 N ≤ ‖(countingRadius38 N : ℂ)‖ := by
    simp [Complex.norm_real, abs_of_pos (countingRadius_pos38 N)]
  have hsep := counting_central_sphere_separated38 N hsphere
  obtain ⟨hs₁, hc₁, he₁⟩ := periodic_counting_at38 φ N hcmp₁
  obtain ⟨hs₂, hc₂, he₂⟩ := critical_counting_at38 φ N hcmp₂
  constructor
  · refine ⟨hN, analyticOnNhd_perChar_z φ,
      ⟨_, counting_ne_zero_of_comparison38 (hcmp₁ _ hnorm hsep)⟩,
      counting_zeroMult_support_finite38 φ, hs₁, ?_, he₁⟩
    omega
  · refine ⟨hN, analyticOnNhd_discrimDeriv38 φ,
      ⟨_, critical_ne_zero_of_comparison38 (hcmp₂ _ hnorm hsep)⟩,
      critical_zeroMult_support_finite38 φ, hs₂, ?_, he₂⟩
    simpa only [one_mul] using hc₂

end
end NlsGge.GK38
