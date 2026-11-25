import NlsGge.GK38.DirichletAsymptotics
import NlsGge.GK38.PeriodicLabelling

/-! # D1: concrete Dirichlet counting with analytic multiplicities

Book Lemma 5.2. The accepted quarter-disc geometry and Rouché theorem are
applied to the actual positive-sine characteristic. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_zeroMult_support_finite38 (φ : PotPair) (c : ℂ) (r : ℝ) :
    (Function.support (Lib.zeroMult (dirichletChar φ) (ball c r))).Finite :=
  Lib.zeroMult_support_finite
    ((analyticOnNhd_dirichletChar_z φ).mono (subset_univ _)).meromorphicOn
    (isCompact_closedBall c r) ball_subset_closedBall

/-- The free Dirichlet and critical functions have identical zero multisets, including orders. -/
theorem dirichlet_free_multiset38 (c : ℂ) (r : ℝ) :
    Lib.zeroMultiset (dirichletChar 0) (ball c r) =
      Lib.zeroMultiset (deriv (discrim 0)) (ball c r) := by
  classical
  have he : dirichletChar 0 = Complex.sin := funext dirichletChar_zero
  apply Multiset.ext'
  intro z
  rw [Lib.count_zeroMultiset_ball ((analyticOnNhd_dirichletChar_z 0).mono (subset_univ _)),
    Lib.count_zeroMultiset_ball ((analyticOnNhd_discrimDeriv38 0).mono (subset_univ _))]
  simp only [he, Lib.order_sin, critical_free_order38]

theorem free_dirichlet_counting38 {N : ℕ} (hN : 0 < N) :
    RootCountingAt38 (dirichletChar 0) 1 N := by
  have h := free_critical_counting38 hN
  refine ⟨hN, analyticOnNhd_dirichletChar_z 0,
    ⟨((Real.pi / 2 : ℝ) : ℂ), by rw [dirichletChar_zero]; exact free_sine_half_ne38⟩,
    dirichlet_zeroMult_support_finite38 0, ?_, ?_, ?_⟩
  · intro n hn
    rw [dirichlet_free_multiset38]
    exact h.2.2.2.2.1 n hn
  · rw [dirichlet_free_multiset38]
    exact h.2.2.2.2.2.1
  · intro z hz
    apply h.2.2.2.2.2.2 z
    apply (critical_free_zero_iff38 z).mpr
    simpa only [dirichletChar_zero] using hz

theorem dirichlet_strict_comparison38 {φ : PotPair} {z : ℂ}
    (herr : ‖dirichletChar φ z - Complex.sin z‖ ≤
      (1 / (2 * sineOffDiscsConstant38)) * Real.exp |z.im|)
    (hsep : ∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) :
    ‖dirichletChar φ z - dirichletChar 0 z‖ < ‖dirichletChar 0 z‖ := by
  have hpos : 0 < ‖Complex.sin z‖ := norm_pos_iff.mpr (counting_sin_ne_zero38 hsep)
  have hb := sine_off_discs_lower_bound38 z hsep
  have hC := sineOffDiscsConstant38_pos
  have hle : (1 / (2 * sineOffDiscsConstant38)) * Real.exp |z.im| ≤
      (1 / 2 : ℝ) * ‖Complex.sin z‖ := by
    apply (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hC)).mp
    have he : 2 * sineOffDiscsConstant38 * ((1 / (2 * sineOffDiscsConstant38)) * Real.exp |z.im|) =
        Real.exp |z.im| := by field_simp
    rw [he]
    nlinarith
  rw [dirichletChar_zero]
  exact (herr.trans hle).trans_lt (by linarith)

theorem dirichlet_ne_zero_of_comparison38 {φ : PotPair} {z : ℂ}
    (h : ‖dirichletChar φ z - dirichletChar 0 z‖ < ‖dirichletChar 0 z‖) :
    dirichletChar φ z ≠ 0 := by
  intro hz
  rw [hz, zero_sub, norm_neg] at h
  exact (lt_irrefl _ h)

/-- A supplied counting radius above the asymptotic threshold is certified directly. -/
theorem dirichlet_counting_at38 (φ : PotPair) (N : ℕ) (hN : 0 < N)
    (hcmp : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖dirichletChar φ z - dirichletChar 0 z‖ < ‖dirichletChar 0 z‖) :
    RootCountingAt38 (dirichletChar φ) 1 N := by
  have hf := analyticOnNhd_dirichletChar_z φ
  have hfree := free_dirichlet_counting38 hN
  have hnz : dirichletChar φ (countingRadius38 N : ℂ) ≠ 0 := by
    apply dirichlet_ne_zero_of_comparison38
    apply hcmp _ (by simp [Complex.norm_real, abs_of_pos (countingRadius_pos38 N)])
    exact counting_central_sphere_separated38 N (counting_radius_mem_sphere38 N)
  refine ⟨hN, hf, ⟨_, hnz⟩, dirichlet_zeroMult_support_finite38 φ, ?_, ?_, ?_⟩
  · intro n hn
    refine Eq.trans ?_ (hfree.2.2.2.2.1 n hn)
    exact Lib.rouche_circle (by positivity : 0 < Real.pi / 4)
      ((analyticOnNhd_dirichletChar_z 0).mono (subset_univ _)) (hf.mono (subset_univ _))
      (fun z hz => hcmp z (counting_far_sphere_norm38 hn hz) (counting_small_sphere_separated38 n hz))
  · refine Eq.trans ?_ hfree.2.2.2.2.2.1
    apply Lib.rouche_circle (countingRadius_pos38 N)
      ((analyticOnNhd_dirichletChar_z 0).mono (subset_univ _)) (hf.mono (subset_univ _))
    intro z hz
    have hz' : countingRadius38 N ≤ ‖z‖ := by
      have he : ‖z‖ = countingRadius38 N := by simpa only [mem_sphere, dist_zero_right] using hz
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
      exact dirichlet_ne_zero_of_comparison38
        (hcmp z hz' (counting_outside_separated38 N hz' hfar)) hz0

/-- Actual common local q=1 counting, with no extra characteristic hypothesis. -/
theorem dirichlet_counting_lemma38 (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ,
      ∀ φ : PotPair, φ ∈ U → RootCountingAt38 (dirichletChar φ) 1 N := by
  obtain ⟨U, hU, R, herr⟩ := dirichletChar_asymp φ₀ (1 / (2 * sineOffDiscsConstant38))
    (one_div_pos.mpr (mul_pos (by norm_num) sineOffDiscsConstant38_pos))
  obtain ⟨K, hK⟩ := exists_nat_gt (R / Real.pi)
  let N : ℕ := K + 1
  have hNpos : 0 < N := Nat.succ_pos K
  have hRN : R ≤ countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    unfold countingRadius38 N
    push_cast
    linarith [Real.pi_pos]
  exact ⟨U, hU, N, fun φ hφ => dirichlet_counting_at38 φ N hNpos
    (fun z hz hsep => dirichlet_strict_comparison38 (herr φ hφ z (hRN.trans hz)) hsep)⟩

end
end NlsGge.GK38
