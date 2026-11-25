import Mathlib
import NlsGge.Atomic.G5.G5001
import NlsGge.Atomic.G5.G5004Host
import NlsGge.Atomic.G5.G5004Support1
import NlsGge.Atomic.G5.G5004Support2
import NlsGge.Atomic.G5.G5004Support3
import NlsGge.GK38.Lib.HilbertValuedAnalytic

/- G5-004 SUPPORT4 (proof development, AUTHOR; not self-reviewed, not accepted). Target
   NlsGge/Atomic/G5/G5004Support4.lean.  Pro round 10 section 7 (commit 178f84d6) route: realize (a_n - (-1)^n)
   as an l2-valued map, analytic by Lib.analyticOnNhd_of_coords_of_locBdd (local bounds from
   radiusOmittedNormalized_local_l2), hence norm continuous, hence a uniform lower bound on |a_n| near the
   reference point.  All helper names are g5004_*; no new definition. -/
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5004_a_ne_zero (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
    radiusOmittedNormalized n φ ≠ 0 := by
  have hA := a5OmittedRoot_ne_zero38 n (φ, muSeq φ n) (g5001_dom φ hφ n)
  have hpi : (Lib.piN n : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
  exact div_ne_zero hA hpi

theorem g5004_realization :
    ∃ F : PotPair → Lib.L2Z, AnalyticOnNhd ℂ F sourceBetaW ∧
      ∀ φ ∈ sourceBetaW, ∀ n : ℤ,
        F φ n = radiusOmittedNormalized n φ - (-1 : ℂ) ^ n := by
  classical
  have hmem : ∀ φ ∈ sourceBetaW,
      Memℓp (fun n : ℤ => radiusOmittedNormalized n φ - (-1 : ℂ) ^ n) 2 := by
    intro φ hφ
    obtain ⟨U, -, hφU, -, B, -, hB⟩ := radiusOmittedNormalized_local_l2 φ hφ
    have hs := (hB φ hφU).1
    exact (memℓp_gen_iff (by simp)).mpr (by simpa using hs)
  let F : PotPair → Lib.L2Z := fun φ =>
    if h : φ ∈ sourceBetaW then ⟨_, hmem φ h⟩ else 0
  have hF : ∀ φ ∈ sourceBetaW, ∀ n : ℤ,
      F φ n = radiusOmittedNormalized n φ - (-1 : ℂ) ^ n := fun φ hφ n => by
    simp [F, hφ]
  refine ⟨F, ?_, hF⟩
  apply Lib.analyticOnNhd_of_coords_of_locBdd F sourceFamily.V_open
  · intro n
    have h1 : AnalyticOnNhd ℂ
        (fun φ : PotPair => radiusOmittedNormalized n φ - (-1 : ℂ) ^ n) sourceBetaW :=
      (radiusOmittedNormalized_analytic n).sub analyticOnNhd_const
    exact h1.congr sourceFamily.V_open (fun φ hφ => (hF φ hφ n).symm)
  · intro φ₀ hφ₀
    obtain ⟨U, hUo, hφU, hUW, B, hB0, hB⟩ := radiusOmittedNormalized_local_l2 φ₀ hφ₀
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUo φ₀ hφU
    refine ⟨r, hr, B + 1, fun y hy => ?_⟩
    have hyU := hrU hy
    have hyW := hUW hyU
    obtain ⟨-, hbd⟩ := hB y hyU
    have hsq : ‖F y‖ ^ 2 =
        ∑' n : ℤ, ‖radiusOmittedNormalized n y - (-1 : ℂ) ^ n‖ ^ 2 := by
      rw [← Lib.tsum_sq_l2]
      exact tsum_congr fun n => by rw [hF y hyW n]
    nlinarith [norm_nonneg (F y)]

theorem g5004_uniform_lower (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
    ∃ d₀ r : ℝ, 0 < d₀ ∧ 0 < r ∧ Metric.ball φ₀ r ⊆ sourceBetaW ∧
      (∀ n : ℤ, d₀ ≤ ‖radiusOmittedNormalized n φ₀‖) ∧
      ∀ φ ∈ Metric.ball φ₀ r, ∀ n : ℤ, d₀ / 2 ≤ ‖radiusOmittedNormalized n φ‖ := by
  obtain ⟨F, hFan, hF⟩ := g5004_realization
  have hne : ∀ n : ℤ, radiusOmittedNormalized n φ₀ ≠ 0 := fun n => g5004_a_ne_zero n φ₀ hφ₀
  obtain ⟨U, hUo, hφU, hUW, B, hB0, hB⟩ := radiusOmittedNormalized_local_l2 φ₀ hφ₀
  have hsum := (hB φ₀ hφU).1
  have ht : Tendsto (fun n : ℤ => ‖radiusOmittedNormalized n φ₀ - (-1 : ℂ) ^ n‖ ^ 2)
      cofinite (𝓝 0) := hsum.tendsto_cofinite_zero
  have hev : ∀ᶠ n in cofinite, (1 / 2 : ℝ) ≤ ‖radiusOmittedNormalized n φ₀‖ := by
    filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))] with n hn
    have h1 : ‖radiusOmittedNormalized n φ₀ - (-1 : ℂ) ^ n‖ < 1 / 2 := by
      by_contra hcon
      have hcon' := not_lt.mp hcon
      nlinarith [norm_nonneg (radiusOmittedNormalized n φ₀ - (-1 : ℂ) ^ n)]
    have hp1 : ‖(-1 : ℂ) ^ n‖ = 1 := by simp
    have h2 := norm_sub_norm_le ((-1 : ℂ) ^ n) (radiusOmittedNormalized n φ₀)
    rw [hp1, norm_sub_rev] at h2
    linarith
  have hfin : {n : ℤ | ¬ (1 / 2 : ℝ) ≤ ‖radiusOmittedNormalized n φ₀‖}.Finite :=
    Filter.eventually_cofinite.mp hev
  have key : ∀ T : Finset ℤ, ∃ d : ℝ, 0 < d ∧ ∀ n ∈ T, d ≤ ‖radiusOmittedNormalized n φ₀‖ := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | insert x T hx ih =>
      obtain ⟨d, hd, hdT⟩ := ih
      refine ⟨min d ‖radiusOmittedNormalized x φ₀‖,
        lt_min hd (norm_pos_iff.mpr (hne x)), fun n hn => ?_⟩
      rcases Finset.mem_insert.mp hn with h | h
      · rw [h]; exact min_le_right _ _
      · exact (min_le_left _ _).trans (hdT n h)
  obtain ⟨d, hd, hdS⟩ := key hfin.toFinset
  set d₀ : ℝ := min d (1 / 2) with hd₀
  have hd₀pos : 0 < d₀ := lt_min hd (by norm_num)
  have hlow0 : ∀ n : ℤ, d₀ ≤ ‖radiusOmittedNormalized n φ₀‖ := fun n => by
    by_cases hn : n ∈ hfin.toFinset
    · exact (min_le_left _ _).trans (hdS n hn)
    · have hn' : (1 / 2 : ℝ) ≤ ‖radiusOmittedNormalized n φ₀‖ := by
        by_contra hcon
        exact hn (hfin.mem_toFinset.mpr hcon)
      exact (min_le_right _ _).trans hn'
  have hcont : ContinuousAt F φ₀ := (hFan φ₀ hφ₀).continuousAt
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.mp hcont (d₀ / 2) (by positivity)
  obtain ⟨r₁, hr₁, hr₁W⟩ := Metric.isOpen_iff.mp sourceFamily.V_open φ₀ hφ₀
  refine ⟨d₀, min δ r₁, hd₀pos, lt_min hδ hr₁, ?_, hlow0, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_right _ _)).trans hr₁W
  · intro φ hφ n
    have hφδ : dist φ φ₀ < δ := lt_of_lt_of_le (Metric.mem_ball.mp hφ) (min_le_left _ _)
    have hφW : φ ∈ sourceBetaW :=
      hr₁W (Metric.ball_subset_ball (min_le_right _ _) hφ)
    have h1 : dist (F φ) (F φ₀) < d₀ / 2 := hδF hφδ
    have h2 : ‖F φ n - F φ₀ n‖ ≤ ‖F φ - F φ₀‖ := by
      have := lp.norm_apply_le_norm (by simp : (2 : ENNReal) ≠ 0) (F φ - F φ₀) n
      simpa using this
    have h3 : F φ n - F φ₀ n =
        radiusOmittedNormalized n φ - radiusOmittedNormalized n φ₀ := by
      rw [hF φ hφW n, hF φ₀ hφ₀ n]; ring
    rw [h3] at h2
    have h4 := norm_sub_norm_le (radiusOmittedNormalized n φ₀) (radiusOmittedNormalized n φ)
    rw [norm_sub_rev] at h4
    rw [dist_eq_norm] at h1
    have := hlow0 n
    linarith

end
end NlsGge.GKDefinitionDesign
