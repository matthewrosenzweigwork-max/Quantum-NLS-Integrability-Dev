import NlsGge.GK38.PeriodicLabellingCriticalFree

/-! # S2: locally uniform critical counting (GK Lemma 6.5, counting part) -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem critical_strict_comparison38 {φ : PotPair} {z : ℂ}
    (herr : ‖deriv (discrim φ) z - (-2 * Complex.sin z)‖ ≤
      (1 / sineOffDiscsConstant38) * Real.exp |z.im|)
    (hsep : ∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) :
    ‖deriv (discrim φ) z - deriv (discrim 0) z‖ < ‖deriv (discrim 0) z‖ := by
  have hpos : 0 < ‖Complex.sin z‖ := norm_pos_iff.mpr (counting_sin_ne_zero38 hsep)
  have hb := sine_off_discs_lower_bound38 z hsep
  have hC := sineOffDiscsConstant38_pos
  have hle : (1 / sineOffDiscsConstant38) * Real.exp |z.im| ≤ ‖Complex.sin z‖ := by
    apply (mul_le_mul_iff_right₀ hC).mp
    calc
      sineOffDiscsConstant38 * ((1 / sineOffDiscsConstant38) * Real.exp |z.im|) =
          Real.exp |z.im| := by field_simp
      _ ≤ sineOffDiscsConstant38 * ‖Complex.sin z‖ := hb
  rw [discrimDeriv_zero38]
  calc
    _ ≤ ‖Complex.sin z‖ := herr.trans hle
    _ < ‖-2 * Complex.sin z‖ := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat]
      linarith

theorem critical_ne_zero_of_comparison38 {φ : PotPair} {z : ℂ}
    (h : ‖deriv (discrim φ) z - deriv (discrim 0) z‖ < ‖deriv (discrim 0) z‖) :
    deriv (discrim φ) z ≠ 0 := by
  intro hz
  rw [hz, zero_sub, norm_neg] at h
  exact (lt_irrefl _ h)

/-- A supplied radius above the uniform comparison threshold is certified directly. -/
theorem critical_counting_at38 (φ : PotPair) (N : ℕ)
    (hcmp : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖deriv (discrim φ) z - deriv (discrim 0) z‖ < ‖deriv (discrim 0) z‖) :
    (∀ n : ℤ, (N : ℤ) < |n| →
      Multiset.card (Lib.zeroMultiset (deriv (discrim φ))
        (ball (countingCenter38 n) (Real.pi / 4))) = 1) ∧
    Multiset.card (Lib.zeroMultiset (deriv (discrim φ))
      (ball (0 : ℂ) (countingRadius38 N))) = 2 * N + 1 ∧
    ∀ z : ℂ, deriv (discrim φ) z = 0 →
      z ∈ ball (0 : ℂ) (countingRadius38 N) ∨
        ∃ n : ℤ, (N : ℤ) < |n| ∧ z ∈ ball (countingCenter38 n) (Real.pi / 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have hfin := critical_zeroMult_support_finite38 φ (countingCenter38 n) (Real.pi / 4)
    refine Eq.trans ?_ (critical_free_small_card38 n)
    refine Lib.rouche_circle (by positivity : 0 < Real.pi / 4)
      ((analyticOnNhd_discrimDeriv38 0).mono (subset_univ _))
      ((analyticOnNhd_discrimDeriv38 φ).mono (subset_univ _)) fun z hz => ?_
    exact hcmp z (counting_far_sphere_norm38 hn hz) (counting_small_sphere_separated38 n hz)
  · have hfin := critical_zeroMult_support_finite38 φ 0 (countingRadius38 N)
    refine Eq.trans ?_ (critical_free_central_card38 N)
    refine Lib.rouche_circle (countingRadius_pos38 N)
      ((analyticOnNhd_discrimDeriv38 0).mono (subset_univ _))
      ((analyticOnNhd_discrimDeriv38 φ).mono (subset_univ _)) fun z hz => ?_
    have hz' : countingRadius38 N ≤ ‖z‖ := by
      have he : ‖z‖ = countingRadius38 N := by
        simpa only [mem_sphere, dist_zero_right] using hz
      exact he.ge
    exact hcmp z hz' (counting_central_sphere_separated38 N hz)
  · intro z hz0
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
      exact critical_ne_zero_of_comparison38
        (hcmp z hz' (counting_outside_separated38 N hz' hfar)) hz0

theorem discrimDeriv_counting_lemma (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, 0 < N ∧
      ∀ φ : PotPair, φ ∈ U →
        (∀ n : ℤ, (N : ℤ) < |n| →
          Multiset.card (Lib.zeroMultiset (deriv (discrim φ))
            (ball (countingCenter38 n) (Real.pi / 4))) = 1) ∧
        Multiset.card (Lib.zeroMultiset (deriv (discrim φ))
          (ball (0 : ℂ) (countingRadius38 N))) = 2 * N + 1 ∧
        ∀ z : ℂ, deriv (discrim φ) z = 0 →
          z ∈ ball (0 : ℂ) (countingRadius38 N) ∨
            ∃ n : ℤ, (N : ℤ) < |n| ∧ z ∈ ball (countingCenter38 n) (Real.pi / 4) := by
  obtain ⟨U, hU, R, herr⟩ := discrimDeriv_asymp φ₀ (1 / sineOffDiscsConstant38)
    (one_div_pos.mpr sineOffDiscsConstant38_pos)
  obtain ⟨K, hK⟩ := exists_nat_gt (R / Real.pi)
  let N : ℕ := K + 1
  have hNpos : 0 < N := Nat.succ_pos K
  have hRN : R ≤ countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    unfold countingRadius38 N
    push_cast
    linarith [Real.pi_pos]
  refine ⟨U, hU, N, hNpos, fun φ hφ => critical_counting_at38 φ N ?_⟩
  intro z hz hsep
  exact critical_strict_comparison38 (herr φ hφ z (hRN.trans hz)) hsep

end
end NlsGge.GK38
