import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCRate

/-! # Trunk C prep (generic), K2 core: rates pass to the closure of a dense set of characters

Author: Claude Opus 5.5 (preparatory author P1, trunk C).  Not self-reviewed, not accepted.
Namespace `NlsGge.ALLS.TransCPrep` (preparatory, `prep_` names).

English interpretation of the declarations.
* `prep_uniform_close_compact {K X} [TopologicalSpace K] [CompactSpace K] [TopologicalSpace X]
  (a : K × X → ℂ) (ha : Continuous a) (x₀) (ε) (hε : 0 < ε)`: a jointly continuous map on
  `K × X` with `K` compact is uniformly continuous in `x` over `K`: for `x` near `x₀`,
  `‖a (k, x) − a (k, x₀)‖ < ε` for every `k ∈ K`.
* `prep_rate_of_dense {X} [TopologicalSpace X] (a : Icc 0 1 × X → ℂ) (ha : Continuous a)
  (D : Set X) (ω₀ : X → ℝ) (hD)`: if `a` is jointly continuous and, for every `x ∈ D` and
  every `t ∈ [0,1]`, `a (t, x) = exp(−(t ω₀ x) i)`, then there is `ω : X → ℝ` that is
  continuous on `closure D`, satisfies `a (t, x) = exp(−(t ω x) i)` for every `x ∈ closure D`
  and every `t ∈ [0,1]`, and agrees with `ω₀` on `D`.  (Route: `rate_close_of_uniform_close`
  makes `ω₀` Cauchy along `𝓝[D] x`; no single-time aliasing because closeness is on all of `[0,1]`.)
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.ALLS.TransCPrep

open Filter Topology

theorem prep_uniform_close_compact {K X : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace X] (a : K × X → ℂ) (ha : Continuous a) (x₀ : X) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ k : K, ‖a (k, x) - a (k, x₀)‖ < ε := by
  let f : C(X × K, ℂ) := ⟨fun q => a (q.2, q.1), ha.comp (continuous_snd.prodMk continuous_fst)⟩
  have h := (f.curry.continuous.tendsto x₀) (Metric.ball_mem_nhds (f.curry x₀) hε)
  filter_upwards [h] with x hx k
  have h1 := ContinuousMap.dist_apply_le_dist (f := f.curry x) (g := f.curry x₀) k
  rw [← dist_eq_norm]
  exact lt_of_le_of_lt h1 hx

/-- Rate closeness on `[0,1]` from closeness of the characters at every `t : Icc 0 1`. -/
theorem prep_rate_close_Icc01 {ω ω' ε : ℝ} (hε : ε < 2)
    (h : ∀ t : Set.Icc (0 : ℝ) 1,
      ‖Complex.exp (-(((t : ℝ) * ω : ℝ) : ℂ) * Complex.I) -
        Complex.exp (-(((t : ℝ) * ω' : ℝ) : ℂ) * Complex.I)‖ ≤ ε) :
    |ω - ω'| ≤ Real.pi * ε / 2 := by
  have := NlsGge.ALLS.TransC.rate_close_of_uniform_close (T := 1) one_pos hε
    (fun t ht => h ⟨t, ht⟩)
  simpa using this

/-- **K2 core** (generic). -/
theorem prep_rate_of_dense {X : Type*} [TopologicalSpace X] (a : Set.Icc (0 : ℝ) 1 × X → ℂ)
    (ha : Continuous a) (D : Set X) (ω₀ : X → ℝ)
    (hD : ∀ x ∈ D, ∀ t : Set.Icc (0 : ℝ) 1,
      a (t, x) = Complex.exp (-(((t : ℝ) * ω₀ x : ℝ) : ℂ) * Complex.I)) :
    ∃ ω : X → ℝ, ContinuousOn ω (closure D) ∧
      (∀ x ∈ closure D, ∀ t : Set.Icc (0 : ℝ) 1,
        a (t, x) = Complex.exp (-(((t : ℝ) * ω x : ℝ) : ℂ) * Complex.I)) ∧
      (∀ x ∈ D, ω x = ω₀ x) := by
  have hpi := Real.pi_pos
  -- a convenient smallness: `ε' = min (1/2) (ε / (2π))`
  have small : ∀ ε > 0, 0 < min (1 / 2 : ℝ) (ε / (2 * Real.pi)) ∧
      2 * min (1 / 2 : ℝ) (ε / (2 * Real.pi)) < 2 ∧
      Real.pi * (2 * min (1 / 2 : ℝ) (ε / (2 * Real.pi))) / 2 < ε := by
    intro ε hε
    refine ⟨lt_min (by norm_num) (by positivity), ?_, ?_⟩
    · have := min_le_left (1 / 2 : ℝ) (ε / (2 * Real.pi)); linarith
    · have h1 := min_le_right (1 / 2 : ℝ) (ε / (2 * Real.pi))
      have h2 : Real.pi * (2 * (ε / (2 * Real.pi))) / 2 = ε / 2 := by field_simp
      have h3 : Real.pi * (2 * min (1 / 2 : ℝ) (ε / (2 * Real.pi))) / 2 ≤
          Real.pi * (2 * (ε / (2 * Real.pi))) / 2 := by gcongr
      linarith
  -- Cauchy along `𝓝[D] x`
  have hlim : ∀ x ∈ closure D, ∃ L : ℝ, Tendsto ω₀ (𝓝[D] x) (𝓝 L) := by
    intro x hx
    have : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
    rw [← cauchy_map_iff_exists_tendsto]
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨hε0, hε2, hεπ⟩ := small ε hε
    set ε' := min (1 / 2 : ℝ) (ε / (2 * Real.pi))
    have hU := prep_uniform_close_compact a ha x ε' hε0
    refine ⟨ω₀ '' (D ∩ {y | ∀ k : Set.Icc (0 : ℝ) 1, ‖a (k, y) - a (k, x)‖ < ε'}),
      image_mem_map (inter_mem_nhdsWithin D hU), ?_⟩
    rintro _ ⟨y, ⟨hyD, hy⟩, rfl⟩ _ ⟨y', ⟨hyD', hy'⟩, rfl⟩
    have hc : ∀ t : Set.Icc (0 : ℝ) 1,
        ‖Complex.exp (-(((t : ℝ) * ω₀ y : ℝ) : ℂ) * Complex.I) -
          Complex.exp (-(((t : ℝ) * ω₀ y' : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * ε' := by
      intro t
      rw [← hD y hyD t, ← hD y' hyD' t]
      calc ‖a (t, y) - a (t, y')‖ ≤ ‖a (t, y) - a (t, x)‖ + ‖a (t, x) - a (t, y')‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε' + ε' := by
            rw [norm_sub_rev (a (t, x))]
            exact add_le_add (hy t).le (hy' t).le
        _ = 2 * ε' := by ring
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (prep_rate_close_Icc01 hε2 hc) hεπ
  let ω : X → ℝ := fun x => limUnder (𝓝[D] x) ω₀
  have hωt : ∀ x ∈ closure D, Tendsto ω₀ (𝓝[D] x) (𝓝 (ω x)) := fun x hx =>
    tendsto_nhds_limUnder (hlim x hx)
  have hchi : ∀ t : ℝ, Continuous (fun w : ℝ => Complex.exp (-((t * w : ℝ) : ℂ) * Complex.I)) := by
    intro t; fun_prop
  have hid : ∀ x ∈ closure D, ∀ t : Set.Icc (0 : ℝ) 1,
      a (t, x) = Complex.exp (-(((t : ℝ) * ω x : ℝ) : ℂ) * Complex.I) := by
    intro x hx t
    have : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
    have h1 : Tendsto (fun y => a (t, y)) (𝓝[D] x) (𝓝 (a (t, x))) :=
      ((ha.comp (continuous_const.prodMk continuous_id)).tendsto x).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun y => Complex.exp (-(((t : ℝ) * ω₀ y : ℝ) : ℂ) * Complex.I)) (𝓝[D] x)
        (𝓝 (Complex.exp (-(((t : ℝ) * ω x : ℝ) : ℂ) * Complex.I))) :=
      ((hchi t).tendsto _).comp (hωt x hx)
    have h3 : (fun y => a (t, y)) =ᶠ[𝓝[D] x]
        fun y => Complex.exp (-(((t : ℝ) * ω₀ y : ℝ) : ℂ) * Complex.I) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hD y hy t
    exact tendsto_nhds_unique (h1.congr' h3) h2
  refine ⟨ω, fun x hx => ?_, hid, fun x hx => ?_⟩
  · rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨hε0, hε2, hεπ⟩ := small ε hε
    set ε' := min (1 / 2 : ℝ) (ε / (2 * Real.pi))
    filter_upwards [nhdsWithin_le_nhds (prep_uniform_close_compact a ha x ε' hε0),
      self_mem_nhdsWithin] with y hy hyD
    have hc : ∀ t : Set.Icc (0 : ℝ) 1,
        ‖Complex.exp (-(((t : ℝ) * ω y : ℝ) : ℂ) * Complex.I) -
          Complex.exp (-(((t : ℝ) * ω x : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * ε' := by
      intro t
      rw [← hid y hyD t, ← hid x hx t]
      have := (hy t).le
      linarith
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (prep_rate_close_Icc01 hε2 hc) hεπ
  · have hc : ∀ t : Set.Icc (0 : ℝ) 1,
        ‖Complex.exp (-(((t : ℝ) * ω x : ℝ) : ℂ) * Complex.I) -
          Complex.exp (-(((t : ℝ) * ω₀ x : ℝ) : ℂ) * Complex.I)‖ ≤ 0 := by
      intro t
      rw [← hid x (subset_closure hx) t, ← hD x hx t, sub_self, norm_zero]
    have h := prep_rate_close_Icc01 (by norm_num) hc
    rw [mul_zero, zero_div] at h
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

end NlsGge.ALLS.TransCPrep
