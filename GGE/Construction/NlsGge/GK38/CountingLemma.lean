import NlsGge.GK38.CountingLemmaFree

/-!
# S1: counting lemma for independent complex potentials

GK Lemma 6.3. One common F5 neighbourhood and a positive natural cutoff
control all far quarter-radius discs and the central disc. Exact free counts
are transferred by Rouché. The same strict comparison directly excludes
zeros outside these discs, including their boundary points.
-/

set_option autoImplicit false

open Filter Topology Set Metric

namespace NlsGge.GK38

noncomputable section

theorem counting_strict_comparison38 {φ : PotPair} {z : ℂ}
    (herr : ‖perChar φ z - (-4 * Complex.sin z ^ 2)‖ ≤ ‖Complex.sin z‖ ^ 2)
    (hsep : ∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) :
    ‖perChar φ z - perChar 0 z‖ < ‖perChar 0 z‖ := by
  have hpos : 0 < ‖Complex.sin z‖ := norm_pos_iff.mpr (counting_sin_ne_zero38 hsep)
  rw [perChar_zero]
  calc
    _ ≤ ‖Complex.sin z‖ ^ 2 := herr
    _ < ‖-4 * Complex.sin z ^ 2‖ := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat, norm_pow]
      nlinarith [sq_pos_of_pos hpos]

theorem counting_ne_zero_of_comparison38 {φ : PotPair} {z : ℂ}
    (h : ‖perChar φ z - perChar 0 z‖ < ‖perChar 0 z‖) : perChar φ z ≠ 0 := by
  intro hz
  rw [hz, zero_sub, norm_neg] at h
  exact (lt_irrefl _ h)

/-- Locally uniform root counts and exhaustive coverage, with analytic multiplicity. -/
theorem counting_lemma (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, ∀ φ : PotPair, φ ∈ U →
      (∀ n : ℤ, (N : ℤ) < |n| →
        Multiset.card (Lib.zeroMultiset (perChar φ)
          (Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4))) = 2) ∧
      Multiset.card (Lib.zeroMultiset (perChar φ)
        (Metric.ball (0 : ℂ) ((N : ℝ) * Real.pi + Real.pi / 4))) = 4 * N + 2 ∧
      ∀ z : ℂ, perChar φ z = 0 →
        z ∈ Metric.ball (0 : ℂ) ((N : ℝ) * Real.pi + Real.pi / 4) ∨
          ∃ n : ℤ, (N : ℤ) < |n| ∧
            z ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) := by
  classical
  obtain ⟨U, hU, R, herr⟩ := perChar_asymp φ₀ 1 (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_gt (R / Real.pi)
  let N : ℕ := K + 1
  have hNpos : 0 < N := Nat.succ_pos K
  have hRN : R ≤ countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    unfold countingRadius38 N
    push_cast
    linarith [Real.pi_pos]
  have hcmp : ∀ φ ∈ U, ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖perChar φ z - perChar 0 z‖ < ‖perChar 0 z‖ := by
    intro φ hφ z hz hsep
    apply counting_strict_comparison38
    · simpa only [one_mul] using herr φ hφ z (hRN.trans hz) hsep
    · exact hsep
  refine ⟨U, hU, N, fun φ hφ => ⟨?_, ?_, ?_⟩⟩
  · intro n hn
    change Multiset.card (Lib.zeroMultiset (perChar φ)
      (ball (countingCenter38 n) (Real.pi / 4))) = 2
    have hfin := counting_zeroMult_support_finite38 φ (countingCenter38 n) (Real.pi / 4)
    refine Eq.trans ?_ (counting_free_small_card38 n)
    refine Lib.rouche_circle (by positivity : 0 < Real.pi / 4)
      ((analyticOnNhd_perChar_z 0).mono (subset_univ _))
      ((analyticOnNhd_perChar_z φ).mono (subset_univ _)) fun z hz => ?_
    exact hcmp φ hφ z (counting_far_sphere_norm38 hn hz)
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
    exact hcmp φ hφ z hz' (counting_central_sphere_separated38 N hz)
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
        (hcmp φ hφ z hz' (counting_outside_separated38 N hz' hfar)) hz0

end
end NlsGge.GK38
