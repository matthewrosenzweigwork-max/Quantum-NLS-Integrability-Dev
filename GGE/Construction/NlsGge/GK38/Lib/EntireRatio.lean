import Mathlib

/-!
# L4a, part 6: two entire functions whose ratio tends to `1` on the circles `|z| = nπ + π/2`

GKP Lemma 20.1/Thm 3.4 pattern (book Lemma 6.8 / Lemma C.5 and its use): if `g` is entire with
zeros contained (with multiplicity) in those of `f`, then `f / g` extends to an entire function
`h`; `‖h - 1‖ → 0` on the circles and the maximum principle give `h = 1`.

The plan's hypothesis placeholder `hgz : ∀ z, g z ≠ 0 ∨ …` is made precise as
`hord : ∀ w, analyticOrderAt g w ≤ analyticOrderAt f w`.  Nonvanishing of `g` on the circles
(for large `n`) is forced by the ratio hypothesis itself (in Lean `f z / 0 = 0`, and `‖0 - 1‖ = 1`).
-/

set_option autoImplicit false

open Filter Topology Metric

namespace NlsGge.GK38.Lib

noncomputable section

/-- The removable-singularity quotient: an entire function `h` with `h z = f z / g z` where `g z ≠ 0`. -/
theorem exists_entire_quotient {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfin : ∀ w, analyticOrderAt g w ≠ ⊤) (hord : ∀ w, analyticOrderAt g w ≤ analyticOrderAt f w) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ z, g z ≠ 0 → h z = f z / g z := by
  set r : ℂ → ℂ := fun z => f z * (g z)⁻¹ with hrdef
  have hfm : ∀ w, MeromorphicAt f w := fun w => (hf.analyticAt w).meromorphicAt
  have hgm : ∀ w, MeromorphicAt g w := fun w => (hg.analyticAt w).meromorphicAt
  have hrm : MeromorphicOn r Set.univ := fun w _ => (hfm w).mul (hgm w).inv
  have hnonneg : ∀ w, 0 ≤ meromorphicOrderAt r w := by
    intro w
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hfin w)
    have hkf : (k : ℕ∞) ≤ analyticOrderAt f w := by rw [hk]; exact hord w
    have hr : r = f * g⁻¹ := rfl
    rw [hr, meromorphicOrderAt_mul (hfm w) (hgm w).inv, meromorphicOrderAt_inv,
      (hf.analyticAt w).meromorphicOrderAt_eq, (hg.analyticAt w).meromorphicOrderAt_eq, ← hk]
    generalize analyticOrderAt f w = o at hkf ⊢
    induction o using ENat.recTopCoe with
    | top => simp
    | coe j =>
      have hjk : k ≤ j := by exact_mod_cast hkf
      simp only [ENat.map_natCast]
      have h0 : (0 : ℤ) ≤ (j : ℤ) + -(k : ℤ) := by omega
      exact_mod_cast h0
  set h' : ℂ → ℂ := toMeromorphicNFOn r Set.univ with halfInvSq'
  have hAn : ∀ w, AnalyticAt ℂ h' w := by
    intro w
    have h1 : AnalyticAt ℂ (toMeromorphicNFAt r w) w :=
      ((hrm w trivial).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt).mp (hnonneg w)
    exact h1.congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hrm trivial).symm
  refine ⟨h', fun w => (hAn w).differentiableAt, fun z hz => ?_⟩
  have hra : AnalyticAt ℂ r z := (hf.analyticAt z).mul ((hg.analyticAt z).inv hz)
  have e1 : toMeromorphicNFAt r z = r := toMeromorphicNFAt_eq_self.mpr hra.meromorphicNFAt
  have e2 : h' z = toMeromorphicNFAt r z z := toMeromorphicNFOn_eq_toMeromorphicNFAt hrm trivial
  rw [e2, e1, hrdef, div_eq_mul_inv]

/-- **Lemma** (maximum principle on the circles `‖z‖ = nπ + π/2`).  See the module doc for the
precise form of the hypothesis on zeros. -/
theorem entire_eq_of_ratio_tendsto_one {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (hord : ∀ w, analyticOrderAt g w ≤ analyticOrderAt f w)
    (h : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ = n * Real.pi + Real.pi / 2 →
      ‖f z / g z - 1‖ < ε) :
    f = g := by
  have hpi := Real.pi_pos
  -- `g` does not vanish on the large circles
  have hcirc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ,
      ‖z‖ = n * Real.pi + Real.pi / 2 → g z ≠ 0 ∧ ‖f z / g z - 1‖ < ε := by
    intro ε hε hε2
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn z hz => ?_⟩
    have h1 := hN n hn z hz
    refine ⟨fun h0 => ?_, h1⟩
    rw [h0, div_zero, zero_sub, norm_neg, norm_one] at h1
    linarith
  obtain ⟨N0, hN0⟩ := hcirc (1 / 2) (by norm_num) le_rfl
  set z0 : ℂ := (((N0 : ℝ) * Real.pi + Real.pi / 2 : ℝ) : ℂ) with hz0
  have hz0n : ‖z0‖ = N0 * Real.pi + Real.pi / 2 := by
    rw [hz0, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hgz0 : g z0 ≠ 0 := (hN0 N0 le_rfl z0 hz0n).1
  have hfin : ∀ w, analyticOrderAt g w ≠ ⊤ := by
    intro w
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (U := Set.univ) (x := z0)
      (fun u _ => hg.analyticAt u) isPreconnected_univ trivial trivial ?_
    rw [(hg.analyticAt z0).analyticOrderAt_eq_zero.mpr hgz0]
    exact ENat.zero_ne_top
  obtain ⟨q, hq, hqe⟩ := exists_entire_quotient hf hg hfin hord
  -- `q = 1`
  have hbound : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ,
      ‖z‖ ≤ n * Real.pi + Real.pi / 2 → ‖q z - 1‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcirc (min ε (1 / 2)) (lt_min hε (by norm_num)) (min_le_right _ _)
    refine ⟨N, fun n hn z hz => ?_⟩
    have hR : 0 < (n : ℝ) * Real.pi + Real.pi / 2 := by positivity
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ)
      ((n : ℝ) * Real.pi + Real.pi / 2)) Metric.isBounded_ball
      ((hq.sub_const 1).diffContOnCl) ?_ ?_
    · intro w hw
      rw [frontier_ball _ hR.ne'] at hw
      have hwn : ‖w‖ = n * Real.pi + Real.pi / 2 := by simpa using hw
      obtain ⟨hgw, hlt⟩ := hN n hn w hwn
      rw [hqe w hgw]
      exact (hlt.trans_le (min_le_left _ _)).le
    · rw [closure_ball _ hR.ne']
      simpa using hz
  have hq1 : ∀ z, q z = 1 := by
    intro z
    by_contra hne
    have hpos : 0 < ‖q z - 1‖ / 2 := by
      have : q z - 1 ≠ 0 := sub_ne_zero.mpr hne
      positivity
    obtain ⟨N, hN⟩ := hbound _ hpos
    obtain ⟨m, hm⟩ := exists_nat_ge (‖z‖ / Real.pi)
    have hle : ‖z‖ ≤ (max N m : ℕ) * Real.pi + Real.pi / 2 := by
      have h1 : (m : ℝ) ≤ ((max N m : ℕ) : ℝ) := by exact_mod_cast le_max_right N m
      have h2 : ‖z‖ ≤ m * Real.pi := by
        rwa [div_le_iff₀ hpi] at hm
      nlinarith
    have := hN (max N m) (le_max_left _ _) z hle
    have h3 : 0 < ‖q z - 1‖ := by
      have : q z - 1 ≠ 0 := sub_ne_zero.mpr hne
      positivity
    linarith
  -- identity theorem
  have hfg : f =ᶠ[𝓝 z0] g := by
    have hnb : ∀ᶠ z in 𝓝 z0, g z ≠ 0 := hg.continuous.continuousAt.eventually_ne hgz0
    filter_upwards [hnb] with z hz
    have := hqe z hz
    rw [hq1 z] at this
    exact (div_eq_one_iff_eq hz).mp this.symm
  funext z
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (fun u _ => hf.analyticAt u)
    (fun u _ => hg.analyticAt u) isPreconnected_univ trivial hfg) trivial

end

end NlsGge.GK38.Lib
