import NlsGge.Composition.SeriesBounds

/-!
# Uniform Cauchy-type series bounds near a compact set of analyticity

Source: `paper/v2.tex` lines 1455-1462 (finite covering, common Cauchy radius).

* `exists_local_series_bounds` : local version at one point of analyticity.
* `exists_uniform_series_bounds` : on a thickening of a compact `K ⊆ O` (`O` open,
  `f` analytic on `O`), there are common `ρ, M` with `f` expanded at every point by a series of
  radius `ρ` and `‖p n‖ ≤ M ρ⁻ⁿ`.
* `exists_uniform_iteratedFDeriv_bounds` : the corollary `‖D^n f y‖ ≤ n! M ρ⁻ⁿ`, with the same
  `δ, ρ, M`.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.Composition

open FormalMultilinearSeries

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Local version: near a point of analyticity, `f` has a power series expansion of a common
radius `ρ` at every point of a ball, with Cauchy bounds `‖p n‖ ≤ C ρ⁻ⁿ`. -/
theorem exists_local_series_bounds {f : E → F} {x : E} (hx : AnalyticAt ℝ f x) :
    ∃ s ρ C : ℝ, 0 < s ∧ 0 < ρ ∧ 0 ≤ C ∧ ∀ y ∈ Metric.ball x s,
      ∃ p : FormalMultilinearSeries ℝ E F,
        HasFPowerSeriesOnBall f p y (ENNReal.ofReal ρ) ∧ ∀ n, ‖p n‖ ≤ C * ρ⁻¹ ^ n := by
  obtain ⟨p, r, hr⟩ := hx
  obtain ⟨r', hr'0, hr'r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hr.r_pos
  have hrad : (r' : ENNReal) < p.radius := lt_of_lt_of_le hr'r hr.r_le
  obtain ⟨C, hC, hCb⟩ := p.norm_mul_pow_le_of_lt_radius hrad
  have hr'pos : (0 : ℝ) < r' := by exact_mod_cast hr'0
  have hbound : ∀ n, ‖p n‖ ≤ C * (r' : ℝ)⁻¹ ^ n := by
    intro n
    have h1 := hCb n
    have h2 : (0 : ℝ) < (r' : ℝ) ^ n := pow_pos hr'pos n
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ h2]
    exact h1
  refine ⟨(r' : ℝ) / 8, (r' : ℝ) / 2, 2 * C, by positivity, by positivity, by positivity, ?_⟩
  intro y hy
  set z : E := y - x with hz
  have hzn : ‖z‖ < (r' : ℝ) / 8 := by
    rw [hz, ← dist_eq_norm]; simpa [Metric.mem_ball] using hy
  have hzle : ‖z‖ ≤ (r' : ℝ) / 4 := by linarith
  have hzr : (‖z‖₊ : ENNReal) < r := by
    refine lt_of_lt_of_le ?_ hr'r.le
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
    simp only [coe_nnnorm]
    linarith
  have hco := hr.changeOrigin hzr
  have hxz : x + z = y := by rw [hz]; abel
  rw [hxz] at hco
  refine ⟨p.changeOrigin z, ?_, ?_⟩
  · refine hco.mono (by positivity) ?_
    have hle : ENNReal.ofReal ((r' : ℝ) / 2) + (‖z‖₊ : ENNReal) ≤ r := by
      refine le_trans ?_ hr'r.le
      have hz' : (‖z‖₊ : ENNReal) = ENNReal.ofReal ‖z‖ := (ofReal_norm z).symm
      rw [hz', ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add
        (by positivity) (norm_nonneg _), ENNReal.ofReal_le_ofReal_iff (by positivity)]
      linarith
    exact ENNReal.le_sub_of_add_le_right ENNReal.coe_ne_top hle
  · intro n
    have := norm_changeOrigin_le p hr'pos hbound hzle n
    calc ‖p.changeOrigin z n‖ ≤ 2 * C * (2 / (r' : ℝ)) ^ n := this
      _ = 2 * C * ((r' : ℝ) / 2)⁻¹ ^ n := by rw [inv_div]

/-- Finite covering: on a thickening of a compact `K ⊆ O`, a common radius `ρ` and constant `M`
such that every point has a power series expansion of radius `ρ` with `‖p n‖ ≤ M ρ⁻ⁿ`. -/
theorem exists_uniform_series_bounds {f : E → F} {O : Set E} (hO : IsOpen O)
    (hf : AnalyticOnNhd ℝ f O) {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ δ ρ M : ℝ, 0 < δ ∧ 0 < ρ ∧ 0 ≤ M ∧ Metric.thickening δ K ⊆ O ∧
      ∀ y ∈ Metric.thickening δ K, ∃ p : FormalMultilinearSeries ℝ E F,
        HasFPowerSeriesOnBall f p y (ENNReal.ofReal ρ) ∧ ∀ n, ‖p n‖ ≤ M * ρ⁻¹ ^ n := by
  classical
  have hloc : ∀ x : E, ∃ s ρ C : ℝ, 0 < s ∧ 0 < ρ ∧ 0 ≤ C ∧
      (x ∈ O → ∀ y ∈ Metric.ball x s, ∃ p : FormalMultilinearSeries ℝ E F,
        HasFPowerSeriesOnBall f p y (ENNReal.ofReal ρ) ∧ ∀ n, ‖p n‖ ≤ C * ρ⁻¹ ^ n) := by
    intro x
    by_cases hxO : x ∈ O
    · obtain ⟨s, ρ, C, hs, hρ, hC, h⟩ := exists_local_series_bounds (hf x hxO)
      exact ⟨s, ρ, C, hs, hρ, hC, fun _ => h⟩
    · exact ⟨1, 1, 0, one_pos, one_pos, le_rfl, fun h => absurd h hxO⟩
  choose s ρ C hs hρ hC hloc using hloc
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (s x))
    (fun x _ => Metric.ball_mem_nhds x (hs x))
  have hU : IsOpen (O ∩ ⋃ x ∈ t, Metric.ball x (s x)) :=
    hO.inter (isOpen_biUnion fun x _ => Metric.isOpen_ball)
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hU
    (fun y hy => ⟨hKO hy, by simpa using hcov hy⟩)
  refine ⟨δ, (1 + ∑ x ∈ t, (ρ x)⁻¹)⁻¹, ∑ x ∈ t, C x, hδ, ?_, ?_,
    fun y hy => (hthick hy).1, ?_⟩
  · have : 0 ≤ ∑ x ∈ t, (ρ x)⁻¹ := Finset.sum_nonneg fun x _ => (inv_pos.2 (hρ x)).le
    positivity
  · exact Finset.sum_nonneg fun x _ => hC x
  · intro y hy
    obtain ⟨hyO, hyU⟩ := hthick hy
    simp only [Set.mem_iUnion] at hyU
    obtain ⟨x, hxt, hyx⟩ := hyU
    obtain ⟨p, hp, hpb⟩ := hloc x (hKO (htK x hxt)) y hyx
    have hS : 0 ≤ ∑ x ∈ t, (ρ x)⁻¹ := Finset.sum_nonneg fun x _ => (inv_pos.2 (hρ x)).le
    have hSx : (ρ x)⁻¹ ≤ ∑ x ∈ t, (ρ x)⁻¹ :=
      Finset.single_le_sum (f := fun x => (ρ x)⁻¹) (fun x _ => (inv_pos.2 (hρ x)).le) hxt
    have hRpos : 0 < (1 + ∑ x ∈ t, (ρ x)⁻¹)⁻¹ := by positivity
    have hinv : (ρ x)⁻¹ ≤ ((1 + ∑ x ∈ t, (ρ x)⁻¹)⁻¹)⁻¹ := by
      rw [inv_inv]; linarith
    have hRle : (1 + ∑ x ∈ t, (ρ x)⁻¹)⁻¹ ≤ ρ x := by
      have := inv_anti₀ (inv_pos.2 (hρ x)) hinv
      simpa using this
    have hCx : C x ≤ ∑ x ∈ t, C x :=
      Finset.single_le_sum (f := fun x => C x) (fun x _ => hC x) hxt
    refine ⟨p, hp.mono (ENNReal.ofReal_pos.2 hRpos) (ENNReal.ofReal_le_ofReal hRle), fun n => ?_⟩
    calc ‖p n‖ ≤ C x * (ρ x)⁻¹ ^ n := hpb n
      _ ≤ (∑ x ∈ t, C x) * ((1 + ∑ x ∈ t, (ρ x)⁻¹)⁻¹)⁻¹ ^ n := by
        exact mul_le_mul hCx (pow_le_pow_left₀ (inv_pos.2 (hρ x)).le hinv n)
          (pow_nonneg (inv_pos.2 (hρ x)).le _) (Finset.sum_nonneg fun x _ => hC x)

/-- Corollary with the same packaging: Cauchy-type bounds for all iterated derivatives,
`‖D^n f y‖ ≤ n! M ρ⁻ⁿ`, on a thickening of `K`. -/
theorem exists_uniform_iteratedFDeriv_bounds {f : E → F} {O : Set E} (hO : IsOpen O)
    (hf : AnalyticOnNhd ℝ f O) {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ δ ρ M : ℝ, 0 < δ ∧ 0 < ρ ∧ 0 ≤ M ∧ Metric.thickening δ K ⊆ O ∧
      (∀ y ∈ Metric.thickening δ K, ∃ p : FormalMultilinearSeries ℝ E F,
        HasFPowerSeriesOnBall f p y (ENNReal.ofReal ρ) ∧ ∀ n, ‖p n‖ ≤ M * ρ⁻¹ ^ n) ∧
      ∀ y ∈ Metric.thickening δ K, ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n f y‖ ≤ n.factorial * M * ρ⁻¹ ^ n := by
  obtain ⟨δ, ρ, M, hδ, hρ, hM, hsub, h⟩ := exists_uniform_series_bounds hO hf hK hKO
  refine ⟨δ, ρ, M, hδ, hρ, hM, hsub, h, fun y hy n => ?_⟩
  obtain ⟨p, hp, hpb⟩ := h y hy
  calc ‖iteratedFDeriv ℝ n f y‖ ≤ n.factorial * ‖p n‖ :=
        norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall hp n
    _ ≤ n.factorial * (M * ρ⁻¹ ^ n) := by gcongr; exact hpb n
    _ = n.factorial * M * ρ⁻¹ ^ n := by ring

end NlsGge.Composition
