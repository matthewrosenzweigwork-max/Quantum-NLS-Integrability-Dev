import NlsGge.Spectral.ActualQuasimomentumE02_38
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # E02.02 (campaign 38, step k3): boundary limit of the actual quasimomentum

At every real `x₀`, the concrete quasimomentum `k = actualQuasimomentumE02_38 u` has a limit
`L` as `z → x₀` within the open upper half-plane, with `cos L = Δh(x₀)` and `0 ≤ Im L`.
Proof: `k z` is eventually within `ε` of the discrete solution set `{±w₀ + 2πn}` of
`cos w = Δh(x₀)` (no bound on `Im`/`Re` is needed); the half-discs are convex, so `k` stays in
one of the disjoint small balls. -/

theorem complex_normSq_sin_eq_E02_38 (w : ℂ) :
    ‖Complex.sin w‖^2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have h : ‖Complex.sin w‖^2 = (Real.sin w.re * Real.cosh w.im)^2 +
      (Real.cos w.re * Real.sinh w.im)^2 := by
    conv_lhs => rw [← Complex.re_add_im w, Complex.sin_add_mul_I]
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  rw [h]
  have h1 := Real.sin_sq_add_cos_sq w.re
  have h2 := Real.cosh_sq w.im
  have h3 : Real.cos w.re ^ 2 = 1 - Real.sin w.re ^ 2 := by linarith
  rw [mul_pow, mul_pow, h2, h3]
  ring

theorem exists_small_sin_near_int_mul_pi_E02_38 (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ ∀ Y : ℂ, ‖Complex.sin Y‖ < s → ∃ n : ℤ, ‖Y - (n:ℂ) * Real.pi‖ < ε := by
  refine ⟨ε/3, by positivity, fun Y hY => ?_⟩
  have hsq := complex_normSq_sin_eq_E02_38 Y
  have hn0 : 0 ≤ ‖Complex.sin Y‖ := norm_nonneg _
  have hs : |Real.sin Y.re| < ε/3 := by
    apply abs_lt_of_sq_lt_sq _ (by positivity)
    nlinarith [sq_nonneg (Real.sinh Y.im), sq_nonneg (ε/3), mul_self_lt_mul_self hn0 hY]
  have hb : |Y.im| < ε/3 := by
    have h1 : |Real.sinh Y.im| < ε/3 := by
      apply abs_lt_of_sq_lt_sq _ (by positivity)
      nlinarith [sq_nonneg (Real.sin Y.re), sq_nonneg (ε/3), mul_self_lt_mul_self hn0 hY]
    have h2 : |Y.im| ≤ Real.sinh |Y.im| := Real.self_le_sinh_iff.mpr (abs_nonneg _)
    rw [← Real.abs_sinh] at h2
    linarith
  set n : ℤ := round (Y.re / Real.pi) with hn
  refine ⟨n, ?_⟩
  set x : ℝ := Y.re - n * Real.pi with hx
  have hpi := Real.pi_pos
  have hxle : |x| ≤ Real.pi / 2 := by
    have := abs_sub_round (Y.re / Real.pi)
    have e : x = Real.pi * (Y.re / Real.pi - n) := by
      rw [hx]; field_simp
    rw [e, abs_mul, abs_of_pos hpi]
    nlinarith
  have hsinx : |Real.sin x| = |Real.sin Y.re| := by
    rw [hx, Real.sin_sub_int_mul_pi, abs_mul]
    simp [abs_zpow]
  have hlow : 2 / Real.pi * |x| ≤ |Real.sin x| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h
        (by rw [abs_of_nonneg h] at hxle; linarith))]
      exact Real.mul_le_sin h (by rw [abs_of_nonneg h] at hxle; exact hxle)
    · have h' : 0 ≤ -x := by linarith
      have hxle' : -x ≤ Real.pi / 2 := by rw [abs_of_nonpos h] at hxle; exact hxle
      have := Real.mul_le_sin h' hxle'
      rw [Real.sin_neg] at this
      rw [abs_of_nonpos h, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h
        (by linarith))]
      exact this
  have hxs : |x| < Real.pi / 2 * (ε/3) := by
    have h1 : 2 / Real.pi * |x| < ε/3 := by
      calc 2 / Real.pi * |x| ≤ |Real.sin x| := hlow
        _ = |Real.sin Y.re| := hsinx
        _ < ε/3 := hs
    have h2 : |x| = Real.pi / 2 * (2 / Real.pi * |x|) := by field_simp
    rw [h2]
    exact mul_lt_mul_of_pos_left h1 (by positivity)
  have hnorm := Complex.norm_le_abs_re_add_abs_im (Y - (n:ℂ) * Real.pi)
  have hre : (Y - (n:ℂ) * Real.pi).re = x := by simp [hx]
  have him : (Y - (n:ℂ) * Real.pi).im = Y.im := by simp
  rw [hre, him] at hnorm
  have : Real.pi / 2 * (ε/3) < ε/3 * 2 := by nlinarith [Real.pi_lt_four]
  linarith


/-- Near-solutions of `cos w = cos w₀` lie near the explicit solution set
`{±w₀ + 2π n}`; no bound on `Im w` is needed. -/
theorem exists_cos_near_solution_E02_38 (w₀ : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ w : ℂ, ‖Complex.cos w - Complex.cos w₀‖ < η →
      ∃ n : ℤ, ‖w - (w₀ + (n:ℂ) * (2 * Real.pi))‖ < ε ∨
        ‖w - (-w₀ + (n:ℂ) * (2 * Real.pi))‖ < ε := by
  obtain ⟨s, hs, hsin⟩ := exists_small_sin_near_int_mul_pi_E02_38 (ε/2) (by positivity)
  refine ⟨2 * s^2, by positivity, fun w hw => ?_⟩
  rw [Complex.cos_sub_cos] at hw
  have hnm : ‖Complex.sin ((w + w₀)/2)‖ * ‖Complex.sin ((w - w₀)/2)‖ < s^2 := by
    have : ‖(-2 : ℂ) * Complex.sin ((w + w₀)/2) * Complex.sin ((w - w₀)/2)‖ =
        2 * (‖Complex.sin ((w + w₀)/2)‖ * ‖Complex.sin ((w - w₀)/2)‖) := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_ofNat]; ring
    rw [this] at hw
    linarith
  by_cases hY : ‖Complex.sin ((w - w₀)/2)‖ < s
  · obtain ⟨n, hn⟩ := hsin _ hY
    refine ⟨n, Or.inl ?_⟩
    have e : w - (w₀ + (n:ℂ) * (2 * Real.pi)) = 2 * ((w - w₀)/2 - (n:ℂ) * Real.pi) := by ring
    rw [e, norm_mul, Complex.norm_ofNat]
    linarith
  · have hX : ‖Complex.sin ((w + w₀)/2)‖ < s := by
      by_contra hX
      push Not at hX hY
      nlinarith [mul_le_mul hX hY hs.le (norm_nonneg _)]
    obtain ⟨n, hn⟩ := hsin _ hX
    refine ⟨n, Or.inr ?_⟩
    have e : w - (-w₀ + (n:ℂ) * (2 * Real.pi)) = 2 * ((w + w₀)/2 - (n:ℂ) * Real.pi) := by ring
    rw [e, norm_mul, Complex.norm_ofNat]
    linarith

/-- Uniform separation of the lattice translates `z + 2π j`, away from zero. -/
theorem exists_lattice_sep_E02_38 (z : ℂ) :
    ∃ d : ℝ, 0 < d ∧ ∀ j : ℤ, z + (j:ℂ) * (2 * Real.pi) ≠ 0 →
      d ≤ ‖z + (j:ℂ) * (2 * Real.pi)‖ := by
  by_cases h : ∃ j₀ : ℤ, z + (j₀:ℂ) * (2 * Real.pi) = 0
  · obtain ⟨j₀, hj₀⟩ := h
    refine ⟨2 * Real.pi, by positivity, fun j hj => ?_⟩
    have e : z + (j:ℂ) * (2 * Real.pi) = (((j - j₀ : ℤ) : ℝ) : ℂ) * (2 * Real.pi) := by
      push_cast
      linear_combination hj₀
    have hne : j - j₀ ≠ 0 := by
      intro h0
      apply hj
      rw [e, h0]; simp
    rw [e, norm_mul]
    have h1 : (1:ℝ) ≤ ‖(((j - j₀ : ℤ) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hne
    have h2 : ‖(2 * (Real.pi:ℂ))‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [h2]
    nlinarith [Real.pi_pos]
  · push Not at h
    let R : Set ℂ := Set.range (fun j : ℤ => z + (j:ℂ) * (2 * Real.pi))
    have hR : IsClosed R := by
      have hint : IsClosed (Set.range ((↑) : ℤ → ℝ)) := Int.isClosedEmbedding_coe_real.isClosed_range
      have h1 : IsClosed (((↑) : ℝ → ℂ) '' Set.range ((↑) : ℤ → ℝ)) :=
        Complex.isUniformEmbedding_ofReal.isClosedEmbedding.isClosedMap _ hint
      let e : ℂ ≃ₜ ℂ := (Homeomorph.mulRight₀ ((2 * Real.pi : ℝ) : ℂ)
        (by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0))).trans (Homeomorph.addLeft z)
      have h2 : IsClosed (e '' (((↑) : ℝ → ℂ) '' Set.range ((↑) : ℤ → ℝ))) :=
        e.isClosedMap _ h1
      convert h2 using 1
      ext w
      simp only [R, Set.mem_range, Set.mem_image, e, Homeomorph.trans_apply,
        Homeomorph.coe_mulRight₀, Homeomorph.coe_addLeft]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨((j:ℝ):ℂ), ⟨(j:ℝ), ⟨j, rfl⟩, rfl⟩, by push_cast; ring⟩
      · rintro ⟨_, ⟨r, ⟨j, rfl⟩, rfl⟩, rfl⟩
        exact ⟨j, by push_cast; ring⟩
    have h0 : (0:ℂ) ∉ R := by
      rintro ⟨j, hj⟩
      exact h j hj
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hR.isOpen_compl 0 h0
    refine ⟨d, hd, fun j _ => ?_⟩
    by_contra hlt
    push Not at hlt
    apply hball (show z + (j:ℂ) * (2 * Real.pi) ∈ Metric.ball (0:ℂ) d by
      rw [mem_ball_zero_iff]; exact hlt)
    exact ⟨j, rfl⟩


/-- A continuous function on a convex set that is, near a boundary point, within `ε` of a
uniformly separated set `S` for every `ε`, has a limit in `S` at that point. -/
theorem exists_tendsto_of_near_separated_set_E02_38 (U : Set ℂ) (hU : Convex ℝ U) (x₀ : ℂ)
    (g : ℂ → ℂ) (hg : ContinuousOn g U) (S : Set ℂ) (d : ℝ) (hd : 0 < d)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → d ≤ ‖p - q‖) [(𝓝[U] x₀).NeBot]
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[U] x₀, ∃ q ∈ S, ‖g z - q‖ < ε) :
    ∃ p ∈ S, Tendsto g (𝓝[U] x₀) (𝓝 p) := by
  have hε₀ : 0 < d / 2 := by positivity
  have hW := hnear (d/2) hε₀
  obtain ⟨r, hr, hH⟩ := Metric.mem_nhdsWithin_iff.mp hW
  set H : Set ℂ := Metric.ball x₀ r ∩ U with hHdef
  have hHmem : H ∈ 𝓝[U] x₀ := Metric.mem_nhdsWithin_iff.mpr ⟨r, hr, subset_rfl⟩
  have hHconv : Convex ℝ H := (convex_ball x₀ r).inter hU
  obtain ⟨z₁, hz₁⟩ := Filter.nonempty_of_mem hHmem
  obtain ⟨p, hpS, hp⟩ := hH hz₁
  have hdisj : ∀ q ∈ S, q ≠ p → ∀ w : ℂ, ‖w - p‖ < d/2 → ‖w - q‖ < d/2 → False := by
    intro q hq hqp w h1 h2
    have := hsep p hpS q hq (Ne.symm hqp)
    have h3 : ‖p - q‖ ≤ ‖w - p‖ + ‖w - q‖ := by
      calc ‖p - q‖ = ‖(w - q) - (w - p)‖ := by congr 1; ring
        _ ≤ ‖w - q‖ + ‖w - p‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith
  have hHsub : ∀ z ∈ H, ‖g z - p‖ < d/2 := by
    let u : Set ℂ := Metric.ball p (d/2)
    let v : Set ℂ := ⋃ q ∈ {q | q ∈ S ∧ q ≠ p}, Metric.ball q (d/2)
    have hu : IsOpen u := Metric.isOpen_ball
    have hv : IsOpen v := isOpen_biUnion (fun q _ => Metric.isOpen_ball)
    have huv : Disjoint u v := by
      rw [Set.disjoint_left]
      intro w hwu hwv
      simp only [v, Set.mem_iUnion, Metric.mem_ball, dist_eq_norm] at hwv
      obtain ⟨q, ⟨hqS, hqp⟩, hwq⟩ := hwv
      exact hdisj q hqS hqp w (by simpa [u, dist_eq_norm] using hwu) hwq
    have hsub : g '' H ⊆ u ∪ v := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨q, hqS, hq⟩ := hH hz
      by_cases hqp : q = p
      · subst hqp
        exact Or.inl (by simpa [u, dist_eq_norm] using hq)
      · exact Or.inr (by
          simp only [v, Set.mem_iUnion, Metric.mem_ball, dist_eq_norm]
          exact ⟨q, ⟨hqS, hqp⟩, hq⟩)
    have hconn : IsPreconnected (g '' H) :=
      hHconv.isPreconnected.image g (hg.mono Set.inter_subset_right)
    rcases hconn.subset_or_subset hu hv huv hsub with h | h
    · intro z hz
      have := h ⟨z, hz, rfl⟩
      simpa [u, dist_eq_norm] using this
    · exfalso
      have h1 : g z₁ ∈ v := h ⟨z₁, hz₁, rfl⟩
      simp only [v, Set.mem_iUnion, Metric.mem_ball, dist_eq_norm] at h1
      obtain ⟨q, ⟨hqS, hqp⟩, hwq⟩ := h1
      exact hdisj q hqS hqp (g z₁) hp hwq
  refine ⟨p, hpS, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < min ε (d/2) := lt_min hε hε₀
  filter_upwards [hHmem, hnear _ hε'] with z hzH hz
  obtain ⟨q, hqS, hq⟩ := hz
  have hq1 : ‖g z - q‖ < d/2 := lt_of_lt_of_le hq (min_le_right _ _)
  have hqp : q = p := by
    by_contra hqp
    exact hdisj q hqS hqp (g z) (hHsub z hzH) hq1
  subst hqp
  rw [dist_eq_norm]
  exact lt_of_lt_of_le hq (min_le_left _ _)


/-- The concrete quasimomentum has a boundary limit at every real point, from the open
upper half-plane. The limit `L` solves `cos L = Δh(x₀)` (half monodromy trace at `x₀`) and
has `0 ≤ Im L`; no real-part or imaginary-part bound is assumed. -/
theorem exists_tendsto_actualQuasimomentum_boundary_E02_38 (u : PhysicalL2) (x₀ : ℝ) :
    ∃ L : ℂ, Tendsto (actualQuasimomentumE02_38 u) (𝓝[{z : ℂ | 0 < z.im}] (x₀:ℂ)) (𝓝 L) ∧
      Complex.cos L = actualPhysicalUnitHalfTrace32 u x₀ ∧ 0 ≤ L.im := by
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hUdef
  set k := actualQuasimomentumE02_38 u with hk
  set Δ := actualPhysicalUnitHalfTrace32 u with hΔ
  have hbr := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  have hkc : ContinuousOn k U := hbr.1.continuousOn
  have hD : Continuous Δ :=
    (analyticOnNhd_actualPhysicalUnitHalfTrace32 u).continuousOn.comp_continuous
      continuous_id (fun _ => Set.mem_univ _)
  have hUconv : Convex ℝ U := convex_halfSpace_im_gt 0
  -- the filter is nontrivial: approach `x₀` along the vertical ray
  have hne : (𝓝[U] (x₀:ℂ)).NeBot := by
    have hpath : Tendsto (fun t : ℝ => (x₀:ℂ) + Complex.I * (t:ℂ)) (𝓝[>] (0:ℝ))
        (𝓝[U] (x₀:ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun t : ℝ => (x₀:ℂ) + Complex.I * (t:ℂ)) := by fun_prop
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [hUdef] using ht
    exact hpath.neBot
  set c : ℂ := Δ (x₀:ℂ) with hc
  obtain ⟨w₀, hw₀⟩ := Complex.cos_surjective c
  set S : Set ℂ := {p : ℂ | ∃ n : ℤ, p = w₀ + (n:ℂ) * (2 * Real.pi) ∨
    p = -w₀ + (n:ℂ) * (2 * Real.pi)} with hS
  have hScos : ∀ p ∈ S, Complex.cos p = c := by
    rintro p ⟨n, rfl | rfl⟩
    · rw [Complex.cos_add_int_mul_two_pi, hw₀]
    · rw [Complex.cos_add_int_mul_two_pi, Complex.cos_neg, hw₀]
  -- uniform separation of `S`
  obtain ⟨d₀, hd₀, hs₀⟩ := exists_lattice_sep_E02_38 0
  obtain ⟨d₁, hd₁, hs₁⟩ := exists_lattice_sep_E02_38 (2 * w₀)
  obtain ⟨d₂, hd₂, hs₂⟩ := exists_lattice_sep_E02_38 (-(2 * w₀))
  have hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → min d₀ (min d₁ d₂) ≤ ‖p - q‖ := by
    rintro p ⟨n, rfl | rfl⟩ q ⟨m, rfl | rfl⟩ hpq
    · have e : (w₀ + (n:ℂ) * (2 * Real.pi)) - (w₀ + (m:ℂ) * (2 * Real.pi)) =
          0 + ((n - m : ℤ):ℂ) * (2 * Real.pi) := by push_cast; ring
      have hpq' := sub_ne_zero.mpr hpq
      rw [e] at hpq' ⊢
      exact (min_le_left _ _).trans (hs₀ _ hpq')
    · have e : (w₀ + (n:ℂ) * (2 * Real.pi)) - (-w₀ + (m:ℂ) * (2 * Real.pi)) =
          2 * w₀ + ((n - m : ℤ):ℂ) * (2 * Real.pi) := by push_cast; ring
      have hpq' := sub_ne_zero.mpr hpq
      rw [e] at hpq' ⊢
      exact ((min_le_right _ _).trans (min_le_left _ _)).trans (hs₁ _ hpq')
    · have e : (-w₀ + (n:ℂ) * (2 * Real.pi)) - (w₀ + (m:ℂ) * (2 * Real.pi)) =
          -(2 * w₀) + ((n - m : ℤ):ℂ) * (2 * Real.pi) := by push_cast; ring
      have hpq' := sub_ne_zero.mpr hpq
      rw [e] at hpq' ⊢
      exact ((min_le_right _ _).trans (min_le_right _ _)).trans (hs₂ _ hpq')
    · have e : (-w₀ + (n:ℂ) * (2 * Real.pi)) - (-w₀ + (m:ℂ) * (2 * Real.pi)) =
          0 + ((n - m : ℤ):ℂ) * (2 * Real.pi) := by push_cast; ring
      have hpq' := sub_ne_zero.mpr hpq
      rw [e] at hpq' ⊢
      exact (min_le_left _ _).trans (hs₀ _ hpq')
  have hdpos : 0 < min d₀ (min d₁ d₂) := lt_min hd₀ (lt_min hd₁ hd₂)
  -- the values `k z` approach `S` as `z → x₀`
  have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[U] (x₀:ℂ), ∃ q ∈ S, ‖k z - q‖ < ε := by
    intro ε hε
    obtain ⟨η, hη, hcos⟩ := exists_cos_near_solution_E02_38 w₀ ε hε
    have h1 : ∀ᶠ z in 𝓝[U] (x₀:ℂ), ‖Δ z - c‖ < η := by
      have hT : Tendsto Δ (𝓝[U] (x₀:ℂ)) (𝓝 c) :=
        (hD.tendsto (x₀:ℂ)).mono_left nhdsWithin_le_nhds
      have := (Metric.tendsto_nhds.mp hT) η hη
      simpa [dist_eq_norm] using this
    filter_upwards [h1, self_mem_nhdsWithin] with z hz hzU
    have hcz : Complex.cos (k z) = Δ z := hbr.2.1 z hzU
    have hz' : ‖Complex.cos (k z) - Complex.cos w₀‖ < η := by rw [hcz, hw₀]; exact hz
    obtain ⟨n, hn | hn⟩ := hcos _ hz'
    · exact ⟨_, ⟨n, Or.inl rfl⟩, hn⟩
    · exact ⟨_, ⟨n, Or.inr rfl⟩, hn⟩
  obtain ⟨p, hpS, hpt⟩ := exists_tendsto_of_near_separated_set_E02_38 U hUconv (x₀:ℂ) k hkc S
    _ hdpos hsep hnear
  refine ⟨p, hpt, hScos p hpS, ?_⟩
  have him : Tendsto (fun z => (k z).im) (𝓝[U] (x₀:ℂ)) (𝓝 p.im) :=
    (Complex.continuous_im.tendsto p).comp hpt
  refine ge_of_tendsto him ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hbr.2.2.1 z hz).le

end NlsGge.SpectralFoundations
end
