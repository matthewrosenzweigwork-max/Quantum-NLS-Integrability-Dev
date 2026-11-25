import NlsGge.GK38.Lib.CircleArgument

/-!
# Rouché, Hurwitz and local constancy of the zero count (library piece L2 of campaign E01)

Local re-proof from Mathlib (E01-D8).  Built on `NlsGge.GK38.Lib.CircleArgument`.

* `rouche_circle`: `‖g - f‖ < ‖f‖` on the boundary circle implies equal zero counts.
* `eventually_card_zeroMultiset_eq`, `zeroCount_locallyConstant`: the zero count in a disc is
  locally constant in a parameter `x` of an arbitrary topological space, provided
  `(x, z) ↦ F x z` is jointly continuous on `X × sphere` (no local compactness of `X` is needed;
  in particular `X` may be an infinite-dimensional Banach space of potentials).
* `hurwitz_circle`: for any filter, uniform convergence on the circle preserves the zero count.

Method for Rouché: with `q = g/f` one has `‖q - 1‖ < 1` on the circle, so `log q` is a smooth
single-valued function of the angle and `∮ (logDeriv g - logDeriv f) = ∮ q'/q = [log q] = 0`.
-/

set_option autoImplicit false

open Complex Metric Set Filter Topology
open scoped Real

namespace NlsGge.GK38.Lib

noncomputable section

section Rouche

variable {c : ℂ} {R : ℝ}

/-- If `‖g - f‖ < ‖f‖` on the circle, then `∮ logDeriv g = ∮ logDeriv f`
(the common value is `2πi` times the zero count). -/
theorem circleIntegral_logDeriv_eq_of_close {f g : ℂ → ℂ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (h : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    (∮ z in C(c, R), logDeriv g z) = ∮ z in C(c, R), logDeriv f z := by
  have hfne : ∀ z ∈ sphere c R, f z ≠ 0 := fun z hz h0 => by
    have := h z hz
    rw [h0, norm_zero] at this
    exact absurd this (not_lt.2 (norm_nonneg _))
  have hgne : ∀ z ∈ sphere c R, g z ≠ 0 := fun z hz h0 => by
    have := h z hz
    rw [h0, zero_sub, norm_neg] at this
    exact absurd this (lt_irrefl _)
  have hint : ∀ k : ℂ → ℂ, AnalyticOnNhd ℂ k (closedBall c R) → (∀ z ∈ sphere c R, k z ≠ 0) →
      CircleIntegrable (logDeriv k) c R := fun k hk hk0 =>
    ContinuousOn.circleIntegrable hR.le fun z hz =>
      (continuousAt_logDeriv' (hk z (sphere_subset_closedBall hz)) (hk0 z hz)).continuousWithinAt
  rw [← sub_eq_zero, ← circleIntegral.integral_sub (hint g hg hgne) (hint f hf hfne)]
  -- the logarithm of the quotient
  set Z : ℝ → ℂ := circleMap c R with hZ
  set D : ℝ → ℂ := fun θ => Complex.log (g (Z θ) / f (Z θ)) with hD
  have hZmem : ∀ θ, Z θ ∈ sphere c R := fun θ => circleMap_mem_sphere c hR.le θ
  have hder : ∀ θ : ℝ, HasDerivAt D
      (deriv (circleMap c R) θ • (logDeriv g (Z θ) - logDeriv f (Z θ))) θ := by
    intro θ
    have hzs := hZmem θ
    have hzc := sphere_subset_closedBall hzs
    have hZd : HasDerivAt Z (circleMap 0 R θ * I) θ := hasDerivAt_circleMap c R θ
    have hgd : HasDerivAt (fun θ => g (Z θ)) ((circleMap 0 R θ * I) • deriv g (Z θ)) θ :=
      HasDerivAt.scomp θ (hg _ hzc).differentiableAt.hasDerivAt hZd
    have hfd : HasDerivAt (fun θ => f (Z θ)) ((circleMap 0 R θ * I) • deriv f (Z θ)) θ :=
      HasDerivAt.scomp θ (hf _ hzc).differentiableAt.hasDerivAt hZd
    have hq := hgd.div hfd (hfne _ hzs)
    -- the quotient lies in the right half plane
    have hre : 0 < (g (Z θ) / f (Z θ)).re := by
      have h1 : ‖g (Z θ) / f (Z θ) - 1‖ < 1 := by
        rw [show g (Z θ) / f (Z θ) - 1 = (g (Z θ) - f (Z θ)) / f (Z θ) by
          field_simp [hfne _ hzs], norm_div, div_lt_one (norm_pos_iff.2 (hfne _ hzs))]
        exact h _ hzs
      have h2 := (abs_re_le_norm (g (Z θ) / f (Z θ) - 1)).trans_lt h1
      rw [sub_re, one_re] at h2
      linarith [(abs_lt.1 h2).1]
    have hslit : g (Z θ) / f (Z θ) ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl hre)
    have := hq.clog_real hslit
    convert this using 1
    rw [deriv_circleMap, smul_eq_mul, logDeriv_apply, logDeriv_apply]
    have hg0 := hgne _ hzs
    have hf0 := hfne _ hzs
    simp only [smul_eq_mul, Pi.div_apply]
    field_simp
  have hDper : D (2 * π) = D 0 := by
    have hp : Z (2 * π) = Z 0 := by simpa using periodic_circleMap c R 0
    simp only [hD, hp]
  have hI : IntervalIntegrable
      (fun θ => deriv (circleMap c R) θ • (logDeriv g (Z θ) - logDeriv f (Z θ)))
      MeasureTheory.volume 0 (2 * π) := by
    have h := (hint g hg hgne).sub (hint f hf hfne)
    simpa [hZ] using (circleIntegrable_iff (c := c) R).1 h
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hder θ) hI
  rw [hDper, sub_self] at key
  change ∫ θ in (0 : ℝ)..2 * π,
    deriv (circleMap c R) θ • (logDeriv g (Z θ) - logDeriv f (Z θ)) = 0
  exact key

/-- **Rouché's theorem on a circle.**  If `f, g` are analytic on the closed disc and
`‖g - f‖ < ‖f‖` on the boundary circle, then `f` and `g` have the same number of zeros in the open
disc, counted with multiplicity. -/
theorem rouche_circle {f g : ℂ → ℂ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (h : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    Multiset.card (zeroMultiset g (ball c R)) = Multiset.card (zeroMultiset f (ball c R)) := by
  have hfne : ∀ z ∈ sphere c R, f z ≠ 0 := fun z hz h0 => by
    have := h z hz
    rw [h0, norm_zero] at this
    exact absurd this (not_lt.2 (norm_nonneg _))
  have hgne : ∀ z ∈ sphere c R, g z ≠ 0 := fun z hz h0 => by
    have := h z hz
    rw [h0, zero_sub, norm_neg] at this
    exact absurd this (lt_irrefl _)
  have h1 := circleIntegral_logDeriv hR hg hgne
  have h2 := circleIntegral_logDeriv hR hf hfne
  rw [circleIntegral_logDeriv_eq_of_close hR hf hg h, h2] at h1
  have h3 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h4 := mul_left_cancel₀ h3 h1
  exact_mod_cast h4.symm

/-- A positive lower bound for `‖f‖` on a circle on which `f` has no zero. -/
theorem exists_pos_le_norm_sphere (hR : 0 < R) {f : ℂ → ℂ} (hf : ContinuousOn f (sphere c R))
    (hne : ∀ z ∈ sphere c R, f z ≠ 0) : ∃ m : ℝ, 0 < m ∧ ∀ z ∈ sphere c R, m ≤ ‖f z‖ := by
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere c R).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hR.le) hf.norm
  exact ⟨‖f z₀‖, norm_pos_iff.2 (hne z₀ hz₀), fun z hz => hmin hz⟩

/-- **Hurwitz's theorem on a circle.**  If `F k → f` uniformly on the circle (along an arbitrary
filter), `F k` and `f` are analytic on the closed disc and `f` has no zero on the circle, then
eventually `F k` has as many zeros in the open disc as `f` (with multiplicity). -/
theorem hurwitz_circle {ι : Type*} (l : Filter ι) {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hR : 0 < R)
    (hF : ∀ᶠ k in l, AnalyticOnNhd ℂ (F k) (closedBall c R))
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hne : ∀ z ∈ sphere c R, f z ≠ 0)
    (hu : TendstoUniformlyOn F f l (sphere c R)) :
    ∀ᶠ k in l, Multiset.card (zeroMultiset (F k) (ball c R)) =
      Multiset.card (zeroMultiset f (ball c R)) := by
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_norm_sphere hR
    (fun z hz => (hf z (sphere_subset_closedBall hz)).continuousAt.continuousWithinAt) hne
  filter_upwards [hF, Metric.tendstoUniformlyOn_iff.1 hu m hm] with k hk hdist
  refine rouche_circle hR hf hk fun z hz => ?_
  have := hdist z hz
  rw [dist_eq_norm, norm_sub_rev] at this
  exact this.trans_le (hmle z hz)

/-- Uniform closeness on a circle, from joint continuity (tube lemma for the compact circle).
The parameter space `X` is an arbitrary topological space. -/
theorem eventually_forall_sphere_norm_sub_lt {X : Type*} [TopologicalSpace X] {F : X → ℂ → ℂ}
    (hcont : ContinuousOn (Function.uncurry F) (univ ×ˢ sphere c R)) (x₀ : X) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ x in 𝓝 x₀, ∀ z ∈ sphere c R, ‖F x z - F x₀ z‖ < ε := by
  have : CompactSpace (sphere c R) := isCompact_iff_compactSpace.1 (isCompact_sphere c R)
  have hc : Continuous (fun p : X × sphere c R => F p.1 p.2) :=
    hcont.comp_continuous (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p => ⟨mem_univ _, p.2.2⟩)
  let Φ : C(X, C(sphere c R, ℂ)) := ContinuousMap.curry ⟨_, hc⟩
  have hev : ∀ᶠ x in 𝓝 x₀, dist (Φ x) (Φ x₀) < ε :=
    (Φ.continuous.tendsto x₀).eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [hev] with x hx z hz
  have := (ContinuousMap.dist_apply_le_dist (f := Φ x) (g := Φ x₀) ⟨z, hz⟩).trans_lt hx
  simpa [Φ, dist_eq_norm] using this

/-- **Local constancy of the zero count at a point** where no zero meets the circle.  The family
`F x` is analytic on the closed disc, `(x, z) ↦ F x z` is jointly continuous on `X × circle`, and
`F x₀` has no zero on the circle: then `x ↦ #zeros(F x)` is eventually equal to its value at `x₀`
near `x₀`. -/
theorem eventually_card_zeroMultiset_eq {X : Type*} [TopologicalSpace X] {F : X → ℂ → ℂ}
    (hR : 0 < R) (hF : ∀ x, AnalyticOnNhd ℂ (F x) (closedBall c R))
    (hcont : ContinuousOn (Function.uncurry F) (univ ×ˢ sphere c R)) (x₀ : X)
    (hne : ∀ z ∈ sphere c R, F x₀ z ≠ 0) :
    ∀ᶠ x in 𝓝 x₀, Multiset.card (zeroMultiset (F x) (ball c R)) =
      Multiset.card (zeroMultiset (F x₀) (ball c R)) := by
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_norm_sphere hR
    (fun z hz => (hF x₀ z (sphere_subset_closedBall hz)).continuousAt.continuousWithinAt) hne
  filter_upwards [eventually_forall_sphere_norm_sub_lt hcont x₀ hm] with x hx
  exact rouche_circle hR (hF x₀) (hF x) fun z hz => (hx z hz).trans_le (hmle z hz)

/-- **The zero count in a disc is locally constant in a parameter.**  `X` is an arbitrary
topological space (e.g. a Banach space of potentials; no local compactness needed),
`F x` is analytic on the closed disc for every `x`, `(x, z) ↦ F x z` is jointly continuous on
`X × circle`, and no `F x` vanishes on the circle. -/
theorem zeroCount_locallyConstant {X : Type*} [TopologicalSpace X] {F : X → ℂ → ℂ}
    (hR : 0 < R) (hF : ∀ x, AnalyticOnNhd ℂ (F x) (closedBall c R))
    (hcont : ContinuousOn (Function.uncurry F) (univ ×ˢ sphere c R))
    (hne : ∀ x, ∀ z ∈ sphere c R, F x z ≠ 0) :
    IsLocallyConstant fun x => Multiset.card (zeroMultiset (F x) (ball c R)) :=
  IsLocallyConstant.iff_eventually_eq _ |>.2 fun x₀ =>
    eventually_card_zeroMultiset_eq hR hF hcont x₀ (hne x₀)

/-- If `f` is analytic on `closedBall a r` (`r > 0`) and vanishes there only at `a`, then its zeros
in the open disc are `a`, repeated `ord_a f` times. -/
theorem zeroMultiset_ball_eq_replicate {f : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall a r)) (h0 : ∀ z ∈ closedBall a r, z ≠ a → f z ≠ 0) :
    zeroMultiset f (ball a r) = Multiset.replicate (analyticOrderNatAt f a) a := by
  classical
  refine Multiset.ext' fun z => ?_
  rw [count_zeroMultiset_ball hf, Multiset.count_replicate]
  by_cases hz : z = a
  · subst hz
    rw [ite_eq_left (mem_ball_self hr), ite_eq_left rfl]
  · rw [ite_eq_right (Ne.symm hz)]
    split_ifs with hzb
    · have hz0 := h0 z (ball_subset_closedBall hzb) hz
      have : analyticOrderAt f z = 0 :=
        (hf z (ball_subset_closedBall hzb)).analyticOrderAt_eq_zero.2 hz0
      simp [analyticOrderNatAt, this]
    · rfl

end Rouche

end

end NlsGge.GK38.Lib
