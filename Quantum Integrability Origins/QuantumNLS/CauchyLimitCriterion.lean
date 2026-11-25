import Mathlib
import QuantumNLS.CauchyUniqueness

/-!
# Deterministic Cauchy-transform criterion for weak convergence of probability measures on `ℝ`

Source use: `ROOT_spectral_measure.tex`, `thm:root-measure`, Steps 3-5: the tail inequality
`ν{|t| > Y} ≤ 2(1 + Y Im G_ν(iY))`, tightness from no loss of mass, extraction of weakly convergent subsequences, identification of
every subsequential limit through its Cauchy transform, and the subsequence criterion for convergence.

The vague-compactness / mass-preserving weak upgrade (contract `FIN-EXT025-GP-10`) is NOT used: the compactness step is mathlib's
Prokhorov theorem `isCompact_closure_of_isTightMeasureSet` for the TIGHT sequences produced here (tightness is derived from the
tail inequality and no loss of mass), and the identification step is `CauchyUniqueness.cauchy_ext`.

Main results (`G_ρ(z) = ∫ (z − t)⁻¹ dρ(t)`, `cauchyTransform`):
* `tail_le`: `ρ{|t| > Y} ≤ 2 (1 + Y Im G_ρ(iY))`;
* `tendsto_cauchy_of_tendsto`: weak convergence implies convergence of `G(z)`, `Im z > 0`;
* `cauchy_ext_dense`: equal `G` on a dense set of points of a horizontal line forces equality of finite measures;
* `exists_subseq_tendsto_of_tight`: Prokhorov in sequential form on `ℝ`;
* `tight_of_cauchy_tail`: tightness of `(ρ_N)` from `G_{ρ_N}(iY_j) → g(iY_j)` and `1 + Y_j Im g(iY_j) → 0`;
* `exists_limit` and `tendsto_of_cauchy`: existence of a probability measure with `G_μ = g` on the line points, and convergence
  `ρ_N → μ` of the whole sequence.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumNLS.CauchyLimitCriterion

open QuantumNLS.CauchyUniqueness (cauchyTransform cauchy_ext integrable_cauchyKernel)

lemma norm_kernel_le {z : ℂ} (hz : 0 < z.im) (t : ℝ) : ‖(z - (t : ℂ))⁻¹‖ ≤ (z.im)⁻¹ := by
  rw [norm_inv]
  have hzq : z.im ≤ ‖z - (t : ℂ)‖ := by
    have := Complex.abs_im_le_norm (z - (t : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  exact inv_anti₀ hz hzq

lemma continuous_kernel {z : ℂ} (hz : 0 < z.im) : Continuous (fun t : ℝ => (z - (t : ℂ))⁻¹) := by
  have hne : ∀ t : ℝ, z - (t : ℂ) ≠ 0 := fun t h => by
    have := congrArg Complex.im h; simp at this; linarith
  exact (continuous_const.sub Complex.continuous_ofReal).inv₀ hne

/-! ### The tail inequality -/

lemma im_cauchy_iY (ρ : Measure ℝ) [IsFiniteMeasure ρ] {Y : ℝ} (hY : 0 < Y) :
    (cauchyTransform ρ (Complex.I * (Y : ℂ))).im = ∫ t : ℝ, -(Y / (t ^ 2 + Y ^ 2)) ∂ρ := by
  have hz : 0 < (Complex.I * (Y : ℂ)).im := by simpa using hY
  unfold cauchyTransform
  have := integral_im (𝕜 := ℂ) (integrable_cauchyKernel ρ hz)
  simp only [RCLike.im_to_complex] at this
  rw [← this]
  congr 1; ext t
  rw [Complex.inv_im]
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, add_zero, sub_zero, zero_add, Complex.normSq_apply,
    Complex.sub_re, Complex.mul_re, mul_zero]
  have : (t ^ 2 + Y ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **Tail inequality** (`ν{|t| > Y} ≤ 2(1 + Y Im G_ν(iY))`). -/
theorem tail_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {Y : ℝ} (hY : 0 < Y) :
    (ρ {t : ℝ | Y < |t|}).toReal ≤ 2 * (1 + Y * (cauchyTransform ρ (Complex.I * (Y : ℂ))).im) := by
  rw [im_cauchy_iY ρ hY]
  set h : ℝ → ℝ := fun t => t ^ 2 / (t ^ 2 + Y ^ 2) with hh
  have hpos : ∀ t : ℝ, 0 < t ^ 2 + Y ^ 2 := fun t => by positivity
  have hcont : Continuous h := by
    refine Continuous.div (by fun_prop) (by fun_prop) (fun t => (hpos t).ne')
  have hbd : ∀ t, ‖h t‖ ≤ 1 := by
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hh]
    simp only
    rw [div_le_one (hpos t)]; nlinarith [sq_nonneg Y]
  have hint : Integrable h ρ :=
    Integrable.mono' (integrable_const (1 : ℝ)) hcont.aestronglyMeasurable
      (Eventually.of_forall hbd)
  have hint2 : Integrable (fun t : ℝ => -(Y / (t ^ 2 + Y ^ 2))) ρ := by
    have hc : Continuous (fun t : ℝ => -(Y / (t ^ 2 + Y ^ 2))) :=
      (continuous_const.div (by fun_prop) (fun t => (hpos t).ne')).neg
    refine Integrable.mono' (integrable_const (Y⁻¹)) hc.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ (hpos t)]
    have : Y⁻¹ * (t ^ 2 + Y ^ 2) ≥ Y := by
      rw [ge_iff_le, ← sub_nonneg]
      have : Y⁻¹ * (t ^ 2 + Y ^ 2) - Y = Y⁻¹ * t ^ 2 := by field_simp; ring
      rw [this]; positivity
    linarith
  have hid : 1 + Y * ∫ t : ℝ, -(Y / (t ^ 2 + Y ^ 2)) ∂ρ = ∫ t : ℝ, h t ∂ρ := by
    have h1 : ∫ t : ℝ, (1 : ℝ) ∂ρ = 1 := by simp
    have : ∀ t : ℝ, 1 + Y * (-(Y / (t ^ 2 + Y ^ 2))) = h t := by
      intro t
      have := (hpos t).ne'
      simp only [hh]; field_simp; ring
    calc 1 + Y * ∫ t : ℝ, -(Y / (t ^ 2 + Y ^ 2)) ∂ρ
        = ∫ t : ℝ, (1 + Y * (-(Y / (t ^ 2 + Y ^ 2)))) ∂ρ := by
          rw [integral_add (integrable_const 1) (hint2.const_mul Y), integral_const_mul, h1]
      _ = ∫ t : ℝ, h t ∂ρ := by simp_rw [this]
  rw [hid]
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := ρ) (f := h)
    (Eventually.of_forall fun t => by simp only [hh]; positivity) hint (1 / 2)
  have hsub : {t : ℝ | Y < |t|} ⊆ {t : ℝ | 1 / 2 ≤ h t} := by
    intro t ht
    simp only [Set.mem_setOf_eq] at ht ⊢
    simp only [hh]
    rw [le_div_iff₀ (hpos t)]
    have : Y ^ 2 < t ^ 2 := by
      have := sq_lt_sq' (by linarith [abs_nonneg t]) ht
      simpa [sq_abs] using this
    nlinarith
  have hmk' : 1 / 2 * (ρ {t : ℝ | 1 / 2 ≤ h t}).toReal ≤ ∫ t : ℝ, h t ∂ρ := hmk
  have hm : (ρ {t : ℝ | Y < |t|}).toReal ≤ (ρ {t : ℝ | 1 / 2 ≤ h t}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  linarith

/-! ### Weak convergence gives convergence of Cauchy transforms -/

theorem tendsto_cauchy_of_tendsto {ι : Type*} {l : Filter ι} {ρ : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (h : Tendsto ρ l (𝓝 μ)) {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun i => cauchyTransform (ρ i : Measure ℝ) z) l (𝓝 (cauchyTransform (μ : Measure ℝ) z)) := by
  have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h
    (BoundedContinuousFunction.ofNormedAddCommGroup (fun t : ℝ => (z - (t : ℂ))⁻¹)
      (continuous_kernel hz) ((z.im)⁻¹) (norm_kernel_le hz))
  exact hf

/-! ### Uniqueness on a dense subset of a line -/

theorem continuous_cauchy_line (ρ : Measure ℝ) [IsFiniteMeasure ρ] {η : ℝ} (hη : 0 < η) :
    Continuous (fun t : ℝ => cauchyTransform ρ ((t : ℂ) + η * Complex.I)) := by
  unfold cauchyTransform
  have hz : ∀ t : ℝ, 0 < ((t : ℂ) + η * Complex.I).im := fun t => by simpa using hη
  refine continuous_of_dominated (bound := fun _ => (η)⁻¹) (fun t => ?_) (fun t => ?_) ?_ ?_
  · exact (continuous_kernel (hz t)).aestronglyMeasurable
  · refine Eventually.of_forall fun s => ?_
    have := norm_kernel_le (hz t) s
    simpa using this
  · exact integrable_const _
  · refine Eventually.of_forall fun s => ?_
    have hne : ∀ t : ℝ, ((t : ℂ) + η * Complex.I) - (s : ℂ) ≠ 0 := fun t h => by
      have := congrArg Complex.im h; simp at this; linarith
    exact ((Complex.continuous_ofReal.add continuous_const).sub continuous_const).inv₀ hne

theorem cauchy_ext_dense (ρ σ : Measure ℝ) [IsFiniteMeasure ρ] [IsFiniteMeasure σ] {η : ℝ} (hη : 0 < η)
    (q : ℕ → ℝ) (hq : DenseRange q)
    (h : ∀ k, cauchyTransform ρ ((q k : ℂ) + η * Complex.I) = cauchyTransform σ ((q k : ℂ) + η * Complex.I)) :
    ρ = σ := by
  refine cauchy_ext ρ σ hη (fun t => ?_)
  have hc1 := continuous_cauchy_line ρ hη
  have hc2 := continuous_cauchy_line σ hη
  have := Continuous.ext_on hq hc1 hc2 (by
    rintro _ ⟨k, rfl⟩
    exact h k)
  exact congrFun this t

/-! ### Prokhorov for tight sequences -/

theorem exists_subseq_tendsto_of_tight (ρ : ℕ → ProbabilityMeasure ℝ)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set ℝ, IsCompact K ∧ ∀ N, (ρ N : Measure ℝ) Kᶜ ≤ ε) :
    ∃ μ : ProbabilityMeasure ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (ρ ∘ φ) atTop (𝓝 μ) := by
  have htight : IsTightMeasureSet {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range ρ} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨K, hK, hKε⟩ := h ε hε
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨_, ⟨N, rfl⟩, rfl⟩
    exact hKε N
  have hcomp := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨μ, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := ρ) (fun N => subset_closure ⟨N, rfl⟩)
  exact ⟨μ, φ, hφ, hlim⟩

/-- Tightness of a sequence from the Cauchy tail inequality and no loss of mass. -/
theorem tight_of_cauchy_tail (ρ : ℕ → ProbabilityMeasure ℝ) (g : ℂ → ℂ) (Y : ℕ → ℝ) (hY : ∀ j, 0 < Y j)
    (hmass : Tendsto (fun j => 1 + Y j * (g (Complex.I * (Y j : ℂ))).im) atTop (𝓝 0))
    (hconv : ∀ j, Tendsto (fun N => cauchyTransform (ρ N : Measure ℝ) (Complex.I * (Y j : ℂ))) atTop
      (𝓝 (g (Complex.I * (Y j : ℂ))))) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set ℝ, IsCompact K ∧ ∀ N, (ρ N : Measure ℝ) Kᶜ ≤ ε := by
  intro ε hε
  obtain ⟨r, hr0, hrε⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ ε := by
    by_cases ht : ε = ⊤
    · exact ⟨1, one_pos, by simp [ht]⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' ht, by rw [ENNReal.ofReal_toReal ht]⟩
  -- choose `j` with `c_j < r/4`
  obtain ⟨j, hj⟩ := (hmass.eventually (gt_mem_nhds (show (0 : ℝ) < r / 4 by positivity))).exists
  -- then eventually in `N`, `1 + Y_j Im G_N < r/2`
  have hN : ∀ᶠ N : ℕ in atTop, 1 + Y j * (cauchyTransform (ρ N : Measure ℝ) (Complex.I * (Y j : ℂ))).im < r / 2 := by
    have h1 : Tendsto (fun N : ℕ => 1 + Y j * (cauchyTransform (ρ N : Measure ℝ) (Complex.I * (Y j : ℂ))).im)
        atTop (𝓝 (1 + Y j * (g (Complex.I * (Y j : ℂ))).im)) :=
      tendsto_const_nhds.add ((Complex.continuous_im.tendsto _).comp (hconv j) |>.const_mul (Y j))
    exact h1.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hN
  -- tails for the finitely many early indices
  have hearly : ∀ N : ℕ, ∃ K : Set ℝ, IsCompact K ∧ (ρ N : Measure ℝ) Kᶜ ≤ ENNReal.ofReal r := by
    intro N
    exact isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
      (isTightMeasureSet_singleton (μ := (ρ N : Measure ℝ))) (ENNReal.ofReal r)
      (by simpa using hr0) |>.imp fun K hK => ⟨hK.1, hK.2 _ rfl⟩
  choose Kf hKf1 hKf2 using hearly
  refine ⟨Metric.closedBall 0 (Y j) ∪ ⋃ N ∈ Finset.range N₁, Kf N, ?_, fun N => ?_⟩
  · exact (isCompact_closedBall _ _).union (Finset.isCompact_biUnion _ fun N _ => hKf1 N)
  · refine le_trans ?_ hrε
    by_cases hN' : N₁ ≤ N
    · have hlt := tail_le (ρ N : Measure ℝ) (hY j)
      have hv := hN₁ N hN'
      have : (ρ N : Measure ℝ) ({t : ℝ | Y j < |t|}) ≤ ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      refine le_trans (measure_mono ?_) this
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_union, Metric.mem_closedBall, dist_zero_right,
        Real.norm_eq_abs, not_or, not_le] at ht
      exact ht.1
    · push Not at hN'
      refine le_trans (measure_mono ?_) (hKf2 N)
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion, not_or] at ht ⊢
      exact fun hmem => ht.2 ⟨N, Finset.mem_range.2 hN', hmem⟩

/-! ### Identification and convergence -/

variable {η₀ : ℝ} {q : ℕ → ℝ} {g : ℂ → ℂ} {Y : ℕ → ℝ}

/-- Every subsequential weak limit of a sequence whose Cauchy transforms converge to `g` on the line points
is determined by `g` there; hence two such limits agree. -/
theorem limit_unique (hη : 0 < η₀) (hq : DenseRange q) {μ μ' : ProbabilityMeasure ℝ}
    (h1 : ∀ k, cauchyTransform (μ : Measure ℝ) ((q k : ℂ) + η₀ * Complex.I) = g ((q k : ℂ) + η₀ * Complex.I))
    (h2 : ∀ k, cauchyTransform (μ' : Measure ℝ) ((q k : ℂ) + η₀ * Complex.I) = g ((q k : ℂ) + η₀ * Complex.I)) :
    μ = μ' := by
  have := cauchy_ext_dense (μ : Measure ℝ) (μ' : Measure ℝ) hη q hq (fun k => by rw [h1 k, h2 k])
  exact Subtype.ext this

/-- **Existence of the limit**: if `G_{ρ_N} → g` at the line points and at `iY_j` with no loss of mass, some probability measure has
`G_μ = g` at the line points. -/
theorem exists_limit (hη : 0 < η₀) (ρ : ℕ → ProbabilityMeasure ℝ) (hY : ∀ j, 0 < Y j)
    (hmass : Tendsto (fun j => 1 + Y j * (g (Complex.I * (Y j : ℂ))).im) atTop (𝓝 0))
    (hconvY : ∀ j, Tendsto (fun N => cauchyTransform (ρ N : Measure ℝ) (Complex.I * (Y j : ℂ))) atTop
      (𝓝 (g (Complex.I * (Y j : ℂ)))))
    (hconvL : ∀ k, Tendsto (fun N => cauchyTransform (ρ N : Measure ℝ) ((q k : ℂ) + η₀ * Complex.I)) atTop
      (𝓝 (g ((q k : ℂ) + η₀ * Complex.I)))) :
    ∃ μ : ProbabilityMeasure ℝ, ∀ k,
      cauchyTransform (μ : Measure ℝ) ((q k : ℂ) + η₀ * Complex.I) = g ((q k : ℂ) + η₀ * Complex.I) := by
  obtain ⟨μ, φ, hφ, hlim⟩ := exists_subseq_tendsto_of_tight ρ (tight_of_cauchy_tail ρ g Y hY hmass hconvY)
  refine ⟨μ, fun k => ?_⟩
  have hz : 0 < ((q k : ℂ) + η₀ * Complex.I).im := by simpa using hη
  have h1 := tendsto_cauchy_of_tendsto hlim hz
  have h2 := (hconvL k).comp hφ.tendsto_atTop
  exact tendsto_nhds_unique h1 h2

/-- **Convergence of the whole sequence**: with the hypotheses of `exists_limit` and a probability measure `μ` having `G_μ = g` at
the line points, `ρ_N → μ` weakly. -/
theorem tendsto_of_cauchy (hη : 0 < η₀) (hq : DenseRange q) (ρ : ℕ → ProbabilityMeasure ℝ)
    (hY : ∀ j, 0 < Y j) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ k, cauchyTransform (μ : Measure ℝ) ((q k : ℂ) + η₀ * Complex.I) = g ((q k : ℂ) + η₀ * Complex.I))
    (hmass : Tendsto (fun j => 1 + Y j * (g (Complex.I * (Y j : ℂ))).im) atTop (𝓝 0))
    (hconvY : ∀ j, Tendsto (fun N => cauchyTransform (ρ N : Measure ℝ) (Complex.I * (Y j : ℂ))) atTop
      (𝓝 (g (Complex.I * (Y j : ℂ)))))
    (hconvL : ∀ k, Tendsto (fun N => cauchyTransform (ρ N : Measure ℝ) ((q k : ℂ) + η₀ * Complex.I)) atTop
      (𝓝 (g ((q k : ℂ) + η₀ * Complex.I)))) :
    Tendsto ρ atTop (𝓝 μ) := by
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  have hY' : ∀ j, Tendsto (fun N => cauchyTransform (ρ (ns N) : Measure ℝ) (Complex.I * (Y j : ℂ))) atTop
      (𝓝 (g (Complex.I * (Y j : ℂ)))) := fun j => (hconvY j).comp hns
  have hL' : ∀ k, Tendsto (fun N => cauchyTransform (ρ (ns N) : Measure ℝ) ((q k : ℂ) + η₀ * Complex.I)) atTop
      (𝓝 (g ((q k : ℂ) + η₀ * Complex.I))) := fun k => (hconvL k).comp hns
  obtain ⟨μ', φ, hφ, hlim⟩ := exists_subseq_tendsto_of_tight (fun N => ρ (ns N))
    (tight_of_cauchy_tail (fun N => ρ (ns N)) g Y hY hmass hY')
  have hμ' : ∀ k, cauchyTransform (μ' : Measure ℝ) ((q k : ℂ) + η₀ * Complex.I) =
      g ((q k : ℂ) + η₀ * Complex.I) := by
    intro k
    have hz : 0 < ((q k : ℂ) + η₀ * Complex.I).im := by simpa using hη
    exact tendsto_nhds_unique (tendsto_cauchy_of_tendsto hlim hz) ((hL' k).comp hφ.tendsto_atTop)
  have : μ' = μ := limit_unique hη hq hμ' hμ
  subst this
  exact ⟨φ, hlim⟩

end QuantumNLS.CauchyLimitCriterion

#print axioms QuantumNLS.CauchyLimitCriterion.tail_le
#print axioms QuantumNLS.CauchyLimitCriterion.tendsto_cauchy_of_tendsto
#print axioms QuantumNLS.CauchyLimitCriterion.cauchy_ext_dense
#print axioms QuantumNLS.CauchyLimitCriterion.exists_subseq_tendsto_of_tight
#print axioms QuantumNLS.CauchyLimitCriterion.tight_of_cauchy_tail
#print axioms QuantumNLS.CauchyLimitCriterion.exists_limit
#print axioms QuantumNLS.CauchyLimitCriterion.tendsto_of_cauchy
