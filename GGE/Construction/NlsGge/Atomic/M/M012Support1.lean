import Mathlib
import NlsGge.Atomic.M.M011Support1

                                                                                                            
                                                                                                          
                                                                                                               
                                                                                                     
                                                                                                                   
                                                                                                                  
                                                                                                   
                                                                                                  
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M012Aux
noncomputable section

open NlsGge.ThirdConsultation.MPrimitive NlsGge.ThirdConsultation.M011Aux

theorem canonRoot_mul_deriv {ψ : PotPair} (hψ : ψ ∈ gkW) {w : ℂ} (hw : w ∈ cutFreeFiber ψ) :
    HasDerivAt (canonRoot38 ψ) (deriv (canonRoot38 ψ) w) w ∧
      canonRoot38 ψ w * deriv (canonRoot38 ψ) w = discrim ψ w * deriv (discrim ψ) w := by
  have hA : AnalyticAt ℂ (canonRoot38 ψ) w :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2) (f := fun z : ℂ => (ψ, z))
      (canonRoot_analytic38 (ψ, w) ⟨hψ, hw⟩) (analyticAt_const.prod analyticAt_id)
  have hR : HasDerivAt (canonRoot38 ψ) (deriv (canonRoot38 ψ) w) w := hA.differentiableAt.hasDerivAt
  have hD : HasDerivAt (discrim ψ) (deriv (discrim ψ) w) w :=
    ((analyticOnNhd_discrim_z ψ) w (mem_univ w)).differentiableAt.hasDerivAt
  refine ⟨hR, ?_⟩
  have h1 := hR.mul hR
  have h2 := (hD.mul hD).sub_const 4
  have heq : (fun z => discrim ψ z * discrim ψ z - 4) =ᶠ[𝓝 w] (fun z => canonRoot38 ψ z * canonRoot38 ψ z) := by
    filter_upwards [(cutFreeFiber_isOpen ψ hψ).mem_nhds hw] with z hz
    have := canonRoot_sq38 ψ hψ z hz
    rw [perChar_eq] at this
    simp only [sq] at this
    exact this.symm
  have hu := (h1.congr_of_eventuallyEq heq).unique h2
  linear_combination hu / 2

theorem log_hasDerivAt {ψ : PotPair} (hψ : ψ ∈ gkW) {K : ℂ} (hK : K ≠ 0) {w : ℂ}
    (hw : w ∈ cutFreeFiber ψ)
    (hs : (discrim ψ w + canonRoot38 ψ w) / K ∈ Complex.slitPlane) :
    HasDerivAt (fun z => Complex.log ((discrim ψ z + canonRoot38 ψ z) / K)) (MContour.omega ψ w) w := by
  obtain ⟨hR, hRR⟩ := canonRoot_mul_deriv hψ hw
  have hD : HasDerivAt (discrim ψ) (deriv (discrim ψ) w) w :=
    ((analyticOnNhd_discrim_z ψ) w (mem_univ w)).differentiableAt.hasDerivAt
  have hf : HasDerivAt (fun z => (discrim ψ z + canonRoot38 ψ z) / K)
      ((deriv (discrim ψ) w + deriv (canonRoot38 ψ) w) / K) w := (hD.add hR).div_const K
  have h := hf.clog hs
  have hR0 : canonRoot38 ψ w ≠ 0 := canonRoot_ne_zero38 ψ hψ w hw
  have hS0 : discrim ψ w + canonRoot38 ψ w ≠ 0 := by
    intro h0
    apply Complex.slitPlane_ne_zero hs
    rw [h0, zero_div]
  refine h.congr_deriv ?_
  unfold MContour.omega
  field_simp
  linear_combination hRR

/-- Nearest-endpoint geometry: the straight path from the endpoint nearer to `z1` meets the cut only at its start. -/
theorem nearest_path_notMem {e e' z1 : ℂ} (hnear : ‖z1 - e‖ ≤ ‖z1 - e'‖)
    (hz1 : z1 ∉ segment ℝ e e') {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    e + (t : ℂ) * (z1 - e) ∉ segment ℝ e e' := by
  intro hmem
  rw [segment_eq_image'] at hmem
  obtain ⟨u, hu, hue⟩ := hmem
  simp only [Complex.real_smul] at hue
  have htu : (t : ℂ) * (z1 - e) = (u : ℂ) * (e' - e) := by linear_combination -hue
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hz1e : z1 - e = ((u / t : ℝ) : ℂ) * (e' - e) := by
    rw [Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff ht0]
    linear_combination htu
  by_cases hs : u / t ≤ 1
  · apply hz1
    rw [segment_eq_image']
    refine ⟨u / t, ⟨div_nonneg hu.1 ht.le, hs⟩, ?_⟩
    simp only [Complex.real_smul]
    linear_combination -hz1e
  · push_neg at hs
    have h1 : ‖z1 - e‖ = (u / t) * ‖e' - e‖ := by
      rw [hz1e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have h2 : z1 - e' = ((u / t - 1 : ℝ) : ℂ) * (e' - e) := by
      rw [Complex.ofReal_sub, Complex.ofReal_one]
      linear_combination hz1e
    have h3 : ‖z1 - e'‖ = (u / t - 1) * ‖e' - e‖ := by
      rw [h2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have h4 : ‖e' - e‖ ≤ 0 := by nlinarith [norm_nonneg (e' - e)]
    have h5 : e' = e := by
      have := norm_le_zero_iff.1 h4
      exact sub_eq_zero.1 this
    apply hz1
    rw [h5] at hz1e ⊢
    have : z1 = e := by
      have h6 : z1 - e = 0 := by simpa using hz1e
      exact sub_eq_zero.1 h6
    rw [this]
    exact left_mem_segment ℝ e e

theorem mem_slitPlane_of_norm_sub_one_lt {x : ℂ} (h : ‖x - 1‖ < 1) : x ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have := Complex.abs_re_le_norm (x - 1)
  rw [Complex.sub_re, Complex.one_re] at this
  have := (abs_lt.1 (lt_of_le_of_lt this h)).1
  linarith

/-- **Collapsed base step.** -/
theorem base_good_collapsed (φ : PotPair) (hφ : φ ∈ gkW) (hgap : lamPlus φ 0 - lamMinus φ 0 = 0) :
    ∃ z1 : ℂ, z1 ∈ cutFreeFiber φ ∧ Good φ z1 := by
  obtain ⟨lam0, hl⟩ : ∃ l : ℂ, lamMinus φ 0 = l := ⟨_, rfl⟩
  have hlp : lamPlus φ 0 = lam0 := by rw [← hl]; exact sub_eq_zero.1 hgap
  obtain ⟨K, hKdef⟩ : ∃ K : ℂ, discrim φ lam0 = K := ⟨_, rfl⟩
  have hroot : ∀ ψ : PotPair, perChar ψ (lamMinus ψ 0) = 0 ∧ perChar ψ (lamPlus ψ 0) = 0 :=
    fun ψ => ⟨(lamSeq_enumeration38 ψ).1 (2 * 0), (lamSeq_enumeration38 ψ).1 (2 * 0 + 1)⟩
  have hK2 : K ^ 2 = 2 ^ 2 := by
    have := (hroot φ).1
    rw [perChar_eq, hl, hKdef] at this
    linear_combination this
  have hKn : ‖K‖ = 2 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hK2 with h | h <;> rw [h] <;> simp
  have hK0 : K ≠ 0 := by intro h; rw [h, norm_zero] at hKn; norm_num at hKn
  -- common isolating family
  obtain ⟨V0, hV0, hV0W, -, -, C, R, hfam⟩ := local_isolatingFamily φ hφ
  have hfφ := hfam φ (mem_of_mem_nhds hV0)
  have hlamB : lam0 ∈ ball (C 0) (R 0) := by
    rw [← hl]; exact Support3Aux.cut_sub_ball hfφ 0 (left_mem_segment ℝ _ _)
  obtain ⟨r0, hr0, hr0sub⟩ := Metric.isOpen_iff.1 isOpen_ball lam0 hlamB
  -- joint continuity of the discriminant at (φ, lam0)
  have hDc : ContinuousAt (fun q : PotPair × ℂ => discrim q.1 q.2) (φ, lam0) :=
    (analyticOnNhd_discrim (φ, lam0) (mem_univ _)).continuousAt
  obtain ⟨ε1, hε1, hD1⟩ := Metric.eventually_nhds_iff_ball.1
    (hDc.eventually_mem (Metric.ball_mem_nhds (discrim φ lam0) (by norm_num : (0 : ℝ) < 1 / 10)))
  rw [hKdef] at hD1
  obtain ⟨r, hr, hrr0, hrε1⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ r0 ∧ r ≤ ε1 :=
    ⟨min r0 ε1, lt_min hr0 hε1, min_le_left _ _, min_le_right _ _⟩
  -- continuity of the gap data at φ
  have hτ0 : tauN φ 0 = lam0 := by rw [tauN_value38 φ hφ 0, hlp, hl]; ring
  have hγ0 : gamma2 φ 0 = 0 := by rw [gamma2_value38 φ hφ 0, hlp, hl]; ring
  have e1 : ∀ᶠ ψ in 𝓝 φ, ψ ∈ V0 := hV0
  have e2 : ∀ᶠ ψ in 𝓝 φ, tauN ψ 0 ∈ ball lam0 (r / 8) := by
    have hc : ContinuousAt (fun ψ : PotPair => tauN ψ 0) φ := (tauN_analytic 0 φ hφ).continuousAt
    have hm : ball lam0 (r / 8) ∈ 𝓝 (tauN φ 0) := by
      rw [hτ0]; exact Metric.ball_mem_nhds _ (by positivity)
    exact hc.eventually_mem hm
  have e3 : ∀ᶠ ψ in 𝓝 φ, gamma2 ψ 0 ∈ ball (0 : ℂ) ((r / 4) ^ 2) := by
    have hc : ContinuousAt (fun ψ : PotPair => gamma2 ψ 0) φ := (gamma2_analytic 0 φ hφ).continuousAt
    have hm : ball (0 : ℂ) ((r / 4) ^ 2) ∈ 𝓝 (gamma2 φ 0) := by
      rw [hγ0]; exact Metric.ball_mem_nhds _ (by positivity)
    exact hc.eventually_mem hm
  obtain ⟨ε2, hε2, hE⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e2.and e3))
  obtain ⟨ε, hε, hεε1, hεε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε1 ∧ ε ≤ ε2 :=
    ⟨min ε1 ε2, lt_min hε1 hε2, min_le_left _ _, min_le_right _ _⟩
  set V : Set PotPair := ball φ ε with hVdef
  have hVε1 : ∀ ψ ∈ V, ψ ∈ ball φ ε1 := fun ψ hψ => ball_subset_ball hεε1 hψ
  have hVε2 : ∀ ψ ∈ V, ψ ∈ ball φ ε2 := fun ψ hψ => ball_subset_ball hεε2 hψ
  have hVW : ∀ ψ ∈ V, ψ ∈ gkW ∧ IsolatingFamily38 ψ C R := fun ψ hψ =>
    ⟨hV0W (hE ψ (hVε2 ψ hψ)).1, hfam ψ (hE ψ (hVε2 ψ hψ)).1⟩
  -- discriminant estimate on the small disc
  have hDest : ∀ ψ ∈ V, ∀ w ∈ ball lam0 r, ‖discrim ψ w - K‖ < 1 / 10 := by
    intro ψ hψ w hw
    have hq : (ψ, w) ∈ ball (φ, lam0) ε1 := by
      rw [← ball_prod_same]
      exact ⟨hVε1 ψ hψ, ball_subset_ball hrε1 hw⟩
    have := hD1 _ hq
    rwa [mem_ball, dist_eq_norm] at this
  -- endpoints of the base cut lie in ball lam0 (r/4)
  have hends : ∀ ψ ∈ V, lamMinus ψ 0 ∈ ball lam0 (r / 4) ∧ lamPlus ψ 0 ∈ ball lam0 (r / 4) := by
    intro ψ hψ
    obtain ⟨-, hτ, hγ⟩ := hE ψ (hVε2 ψ hψ)
    have hW := (hVW ψ hψ).1
    have hτv := tauN_value38 ψ hW 0
    have hγv := gamma2_value38 ψ hW 0
    rw [mem_ball, dist_eq_norm] at hτ
    rw [mem_ball, dist_zero_right, hγv, norm_pow] at hγ
    have hd : ‖lamPlus ψ 0 - lamMinus ψ 0‖ < r / 4 := by
      by_contra hcon
      push_neg at hcon
      have : (r / 4) ^ 2 ≤ ‖lamPlus ψ 0 - lamMinus ψ 0‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcon 2
      linarith
    constructor
    · rw [mem_ball, dist_eq_norm]
      have : lamMinus ψ 0 - lam0 = (tauN ψ 0 - lam0) - (lamPlus ψ 0 - lamMinus ψ 0) / 2 := by
        rw [hτv]; ring
      rw [this]
      calc ‖(tauN ψ 0 - lam0) - (lamPlus ψ 0 - lamMinus ψ 0) / 2‖
          ≤ ‖tauN ψ 0 - lam0‖ + ‖(lamPlus ψ 0 - lamMinus ψ 0) / 2‖ := norm_sub_le _ _
        _ < r / 4 := by
          rw [norm_div, Complex.norm_two]; linarith
    · rw [mem_ball, dist_eq_norm]
      have : lamPlus ψ 0 - lam0 = (tauN ψ 0 - lam0) + (lamPlus ψ 0 - lamMinus ψ 0) / 2 := by
        rw [hτv]; ring
      rw [this]
      calc ‖(tauN ψ 0 - lam0) + (lamPlus ψ 0 - lamMinus ψ 0) / 2‖
          ≤ ‖tauN ψ 0 - lam0‖ + ‖(lamPlus ψ 0 - lamMinus ψ 0) / 2‖ := norm_add_le _ _
        _ < r / 4 := by
          rw [norm_div, Complex.norm_two]; linarith
  have hcut : ∀ ψ ∈ V, segment ℝ (lamMinus ψ 0) (lamPlus ψ 0) ⊆ ball lam0 (r / 4) := fun ψ hψ =>
    (convex_ball lam0 (r / 4)).segment_subset (hends ψ hψ).1 (hends ψ hψ).2
  have hrsub : ball lam0 r ⊆ ball (C 0) (R 0) := (ball_subset_ball hrr0).trans hr0sub
  -- fiber membership in the small disc
  have hfib : ∀ ψ ∈ V, ∀ w ∈ ball lam0 r, w ∉ segment ℝ (lamMinus ψ 0) (lamPlus ψ 0) →
      w ∈ cutFreeFiber ψ := by
    intro ψ hψ w hw hown
    show w ∉ gapSegments38 ψ
    intro hmem
    simp only [gapSegments38, Set.mem_iUnion] at hmem
    obtain ⟨m, hm⟩ := hmem
    by_cases hm0 : m = 0
    · subst hm0; exact hown hm
    · have hf := (hVW ψ hψ).2
      exact Support3Aux.balls_disjoint hf hm0 (Support3Aux.cut_sub_ball hf m hm) (hrsub hw)
  -- the slit-plane estimate
  have hslit : ∀ ψ ∈ V, ∀ w ∈ ball lam0 r, w ∈ cutFreeFiber ψ →
      ‖(discrim ψ w + canonRoot38 ψ w) / K - 1‖ < 1 := by
    intro ψ hψ w hw hwf
    have hd := hDest ψ hψ w hw
    have hsq := canonRoot_sq38 ψ (hVW ψ hψ).1 w hwf
    rw [perChar_eq] at hsq
    have hfac : canonRoot38 ψ w ^ 2 = (discrim ψ w - K) * (discrim ψ w + K) := by
      rw [hsq]; linear_combination hK2
    have hplus : ‖discrim ψ w + K‖ ≤ ‖discrim ψ w - K‖ + 4 := by
      have : discrim ψ w + K = (discrim ψ w - K) + 2 * K := by ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_two, hKn]; linarith
    have hR2 : ‖canonRoot38 ψ w‖ ^ 2 < 1 := by
      rw [← norm_pow, hfac, norm_mul]
      have h0 := norm_nonneg (discrim ψ w - K)
      have h1 : ‖discrim ψ w - K‖ * ‖discrim ψ w + K‖ ≤ ‖discrim ψ w - K‖ * (‖discrim ψ w - K‖ + 4) :=
        mul_le_mul_of_nonneg_left hplus h0
      nlinarith
    have hR1 : ‖canonRoot38 ψ w‖ < 1 := by
      by_contra hcon; push_neg at hcon; nlinarith
    have : (discrim ψ w + canonRoot38 ψ w) / K - 1 = ((discrim ψ w - K) + canonRoot38 ψ w) / K := by
      rw [eq_div_iff hK0, sub_mul, div_mul_cancel₀ _ hK0]
      ring
    rw [this, norm_div, hKn, div_lt_one (by norm_num : (0 : ℝ) < 2)]
    refine (norm_add_le _ _).trans_lt ?_
    linarith
  -- the point z1
  obtain ⟨z1, hz1def⟩ : ∃ z : ℂ, z = lam0 + ((r / 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hz1d : ‖z1 - lam0‖ = r / 2 := by
    rw [hz1def, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hz1B : z1 ∈ ball lam0 r := by rw [mem_ball, dist_eq_norm, hz1d]; linarith
  have hz1own : ∀ ψ ∈ V, z1 ∉ segment ℝ (lamMinus ψ 0) (lamPlus ψ 0) := by
    intro ψ hψ h
    have := hcut ψ hψ h
    rw [mem_ball, dist_eq_norm, hz1d] at this
    linarith
  have hz1f : ∀ ψ ∈ V, z1 ∈ cutFreeFiber ψ := fun ψ hψ => hfib ψ hψ z1 hz1B (hz1own ψ hψ)
  -- the representative
  set Fr : PotPair → ℂ := fun ψ => Complex.log ((discrim ψ z1 + canonRoot38 ψ z1) / K) with hFr
  have hFan : AnalyticOnNhd ℂ Fr V := by
    intro ψ hψ
    have hD : AnalyticAt ℂ (fun ψ : PotPair => discrim ψ z1) ψ :=
      (analyticOnNhd_discrim_phi z1) ψ (mem_univ _)
    have hRa : AnalyticAt ℂ (fun ψ : PotPair => canonRoot38 ψ z1) ψ :=
      AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2) (f := fun ψ : PotPair => (ψ, z1))
        (canonRoot_analytic38 (ψ, z1) ⟨(hVW ψ hψ).1, hz1f ψ hψ⟩) (analyticAt_id.prod analyticAt_const)
    exact ((hD.add hRa).div_const (c := K)).clog
      (mem_slitPlane_of_norm_sub_one_lt (hslit ψ hψ z1 hz1B (hz1f ψ hψ)))
  have hval : ∀ ψ ∈ V, ∀ hp : ψ ∈ gkW ∧ z1 ∈ endpointClosureFiber ψ,
      Fr ψ = M.primitive ⟨(ψ, z1), hp⟩ := by
    intro ψ hψ hp
    have hW := hp.1
    set U : Set ℂ := ball lam0 r ∩ cutFreeFiber ψ with hU
    set F : ℂ → ℂ := fun z => Complex.log ((discrim ψ z + canonRoot38 ψ z) / K) with hF
    have hFd : ∀ z ∈ U, HasDerivAt F (MContour.omega ψ z) z := fun z hz =>
      log_hasDerivAt hW hK0 hz.2 (mem_slitPlane_of_norm_sub_one_lt (hslit ψ hψ z hz.1 hz.2))
    have hωc : ContinuousOn (MContour.omega ψ) U :=
      (omega_differentiableOn_fiber ψ hW).continuousOn.mono inter_subset_right
    -- endpoint limit of F
    have hlim : ∀ e : ℂ, (e = lamMinus ψ 0 ∨ e = lamPlus ψ 0) → Tendsto F (𝓝[U] e) (𝓝 0) := by
      intro e he
      have heB : e ∈ ball lam0 r := by
        rcases he with h | h <;> rw [h]
        · exact ball_subset_ball (by linarith) (hends ψ hψ).1
        · exact ball_subset_ball (by linarith) (hends ψ hψ).2
      have hpe : perChar ψ e = 0 := by
        rcases he with h | h
        · rw [h]; exact (hroot ψ).1
        · rw [h]; exact (hroot ψ).2
      have hKe : discrim ψ e = K := by
        have h2 : discrim ψ e ^ 2 = K ^ 2 := by
          rw [perChar_eq] at hpe; linear_combination hpe - hK2
        have hd := hDest ψ hψ e heB
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
        · exact h
        · exfalso
          rw [h, show -K - K = (-2 : ℂ) * K by ring, norm_mul, norm_neg, Complex.norm_two, hKn] at hd
          norm_num at hd
      have hcD : Continuous (discrim ψ) := continuousOn_univ.mp (analyticOnNhd_discrim_z ψ).continuousOn
      have hDt : Tendsto (discrim ψ) (𝓝[U] e) (𝓝 K) := by
        have := (hcD.continuousAt (x := e)).tendsto.mono_left (nhdsWithin_le_nhds (s := U))
        rwa [hKe] at this
      have hPt : Tendsto (perChar ψ) (𝓝[U] e) (𝓝 0) := by
        have hc : Continuous (perChar ψ) := by
          have : perChar ψ = fun z => discrim ψ z ^ 2 - 4 := funext (perChar_eq ψ)
          rw [this]
          exact (hcD.pow 2).sub continuous_const
        have := (hc.continuousAt (x := e)).tendsto.mono_left (nhdsWithin_le_nhds (s := U))
        rwa [hpe] at this
      have hRt : Tendsto (canonRoot38 ψ) (𝓝[U] e) (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have h1 : Tendsto (fun z => ‖perChar ψ z‖) (𝓝[U] e) (𝓝 0) := by
          simpa using hPt.norm
        have h2 : Tendsto (fun z => Real.sqrt ‖perChar ψ z‖) (𝓝[U] e) (𝓝 0) := by
          have := (Real.continuous_sqrt.tendsto 0).comp h1
          rw [Real.sqrt_zero] at this
          exact this
        refine h2.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        rw [← canonRoot_sq38 ψ hW z hz.2, norm_pow, Real.sqrt_sq (norm_nonneg _)]
      have hft : Tendsto (fun z => (discrim ψ z + canonRoot38 ψ z) / K) (𝓝[U] e) (𝓝 1) := by
        have := (hDt.add hRt).div_const K
        rwa [add_zero, div_self hK0] at this
      have hlog := ((continuousAt_clog Complex.one_mem_slitPlane).tendsto).comp hft
      rw [Complex.log_one] at hlog
      exact hlog
    -- nearest endpoint and the straight path
    obtain ⟨upper, e, e', hebase, hee', hnear⟩ : ∃ (upper : Bool) (e e' : ℂ),
        baseEndpoint ψ upper = e ∧
        segment ℝ e e' = segment ℝ (lamMinus ψ 0) (lamPlus ψ 0) ∧ ‖z1 - e‖ ≤ ‖z1 - e'‖ := by
      by_cases h : ‖z1 - lamMinus ψ 0‖ ≤ ‖z1 - lamPlus ψ 0‖
      · exact ⟨false, lamMinus ψ 0, lamPlus ψ 0, baseEndpoint_false ψ, rfl, h⟩
      · push_neg at h
        exact ⟨true, lamPlus ψ 0, lamMinus ψ 0, baseEndpoint_true ψ, segment_symm ℝ _ _, h.le⟩
    have heE : e = lamMinus ψ 0 ∨ e = lamPlus ψ 0 := by
      cases upper
      · left; rw [← hebase, baseEndpoint_false]
      · right; rw [← hebase, baseEndpoint_true]
    have heB : e ∈ ball lam0 r := by
      rcases heE with h | h <;> rw [h]
      · exact ball_subset_ball (by linarith) (hends ψ hψ).1
      · exact ball_subset_ball (by linarith) (hends ψ hψ).2
    set p : ℝ → ℂ := fun t => e + (t : ℂ) * (z1 - e) with hpdef
    have hpcd : ContDiff ℝ 1 p := contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
    have hpU : ∀ t ∈ Ioc (0 : ℝ) 1, p t ∈ U := by
      intro t ht
      have hB : p t ∈ ball lam0 r := by
        show e + (t : ℂ) * (z1 - e) ∈ ball lam0 r
        have := (convex_ball lam0 r).add_smul_sub_mem heB hz1B (Ioc_subset_Icc_self ht)
        simpa [Complex.real_smul] using this
      refine ⟨hB, hfib ψ hψ _ hB ?_⟩
      rw [← hee']
      exact nearest_path_notMem hnear (by rw [hee']; exact hz1own ψ hψ) ht.1 ht.2
    have hp0 : p 0 = e := by simp [hpdef]
    have hp1 : p 1 = z1 := by simp [hpdef]
    have hE : MContour.HasEndpointIntegral ψ p (F z1 - 0) := by
      refine MContour.endpointIntegral_of_primitive ψ U hωc F hFd p hpcd.continuous.continuousOn
        hpcd.contDiffOn (fun t ht => hpU t (Ioo_subset_Ioc_self ht)) 0 (F z1) ?_ ?_
      · rw [hp0]; exact hlim e heE
      · rw [hp1]
        exact (hFd z1 ⟨hz1B, hz1f ψ hψ⟩).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hadm : AdmissiblePrimitiveChain ψ (baseEndpoint ψ upper) z1 0 (fun _ => p) := by
      refine ⟨fun i => i.elim0, fun _ => ⟨hpcd.continuous.continuousOn, hpcd.contDiffOn⟩,
        by rw [hebase]; exact hp0, hp1,
        Or.inl ⟨fun _ t ht => (hpU t (Ioo_subset_Ioc_self ht)).2, fun i => i.elim0⟩⟩
    obtain ⟨I, hI, hsum⟩ :=
      (symmetric_primitive_characterization ⟨(ψ, z1), hp⟩).2.2 upper 0 (fun _ => p) hadm
    rw [Fin.sum_univ_one] at hsum
    have h1 := MContour.HasEndpointIntegral.unique (hI 0) hE
    show Fr ψ = symmetricPrimitive _
    rw [← hsum, h1, sub_zero]
  refine ⟨z1, hz1f φ (mem_ball_self hε), V, isOpen_ball, mem_ball_self hε, Fr,
    fun ψ hψ => ⟨⟨(hVW ψ hψ).1, hz1f ψ hψ⟩, hval ψ hψ⟩, hFan⟩

end
end NlsGge.ThirdConsultation.M012Aux
