import QuantumNLS.LocalHeight
import QuantumNLS.LabelJointWeak

/-! R-F4C3E5BE CC:F04:selection (root_response/F04.tex:202), stage S2 core: the rank bracketing of
the printed proof ("the rank fraction `i_N/N` tends to `alpha`; for any `x < r_j` sufficiently close
to `r_j` the cumulative mass at `x` is strictly below `alpha` ...; weak empirical convergence,
atomlessness and ordering give `x < q_{i_N} < y` for all large `N`").  Pure measure theory over the
`LocalHeight` conventions (`N + 1` particles, `EmpiricalWeakConv`): no Bethe equation is used. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace QuantumNLS.F04SelRank
open QuantumNLS.LabelJointWeak QuantumNLS.LocalHeight

/-- The empirical probability measure of `N + 1` points. -/
def empP {N : ℕ} (q : Fin (N + 1) → ℝ) : ProbabilityMeasure ℝ :=
  ⟨emp q, ⟨emp_univ q (Nat.succ_pos N)⟩⟩

/-- A probability `Measure` as a `ProbabilityMeasure`. -/
def pmOf (μ : Measure ℝ) [IsProbabilityMeasure μ] : ProbabilityMeasure ℝ := ⟨μ, inferInstance⟩

theorem pmOf_coe (μ : Measure ℝ) [IsProbabilityMeasure μ] : (pmOf μ : Measure ℝ) = μ := rfl

theorem pm_real (ν : ProbabilityMeasure ℝ) (S : Set ℝ) :
    ((ν S : ℝ≥0) : ℝ) = (ν : Measure ℝ).real S := by
  have h := ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν S
  rw [Measure.real, ← h, ENNReal.coe_toReal]

open Classical in
/-- Number of the `N + 1` points lying in `S`. -/
def cnt {N : ℕ} (q : Fin (N + 1) → ℝ) (S : Set ℝ) : ℕ := (Finset.univ.filter fun j => q j ∈ S).card

theorem mem_cnt {N : ℕ} (q : Fin (N + 1) → ℝ) (S : Set ℝ) (T : Finset (Fin (N + 1)))
    (h : ∀ j ∈ T, q j ∈ S) : T.card ≤ cnt q S := by
  classical
  unfold cnt
  exact Finset.card_le_card fun j hj => by simp [h j hj]

theorem cnt_le {N : ℕ} (q : Fin (N + 1) → ℝ) (S : Set ℝ) (T : Finset (Fin (N + 1)))
    (h : ∀ j, q j ∈ S → j ∈ T) : cnt q S ≤ T.card := by
  classical
  unfold cnt
  exact Finset.card_le_card fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact h j hj

theorem empP_apply {N : ℕ} (q : Fin (N + 1) → ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    (((empP q) S : ℝ≥0) : ℝ) = ((N : ℝ) + 1)⁻¹ * (cnt q S : ℝ) := by
  rw [pm_real]
  change (emp q).real S = _
  rw [Measure.real, emp_apply _ hS, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have h1 : (((N : ℝ≥0∞) + 1).toReal) = (N : ℝ) + 1 := by
    rw [ENNReal.toReal_add (ENNReal.natCast_ne_top N) ENNReal.one_ne_top]; simp
  simp [cnt, h1]

theorem integral_empP {N : ℕ} (q : Fin (N + 1) → ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(empP q : Measure ℝ) = ((N : ℝ) + 1)⁻¹ * ∑ j, f (q j) := by
  change ∫ x, f x ∂(emp q) = _
  rw [integral_emp]
  simp

/-- `EmpiricalWeakConv` is weak convergence of the empirical probability measures. -/
theorem weakConv_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ] {q : (N : ℕ) → Fin (N + 1) → ℝ}
    (hw : EmpiricalWeakConv q μ) :
    Tendsto (fun N => empP (q N)) atTop (𝓝 (pmOf μ)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have h := hw f
  have hlim : ∫ ω, f ω ∂(pmOf μ : Measure ℝ) = ∫ y, f y ∂μ := rfl
  rw [hlim]
  refine Tendsto.congr (fun N => ?_) h
  rw [integral_empP, one_div]

theorem tendsto_weakConv {μ : Measure ℝ} [IsProbabilityMeasure μ] {q : (N : ℕ) → Fin (N + 1) → ℝ}
    (h : Tendsto (fun N => empP (q N)) atTop (𝓝 (pmOf μ))) : EmpiricalWeakConv q μ := by
  intro f
  have h2 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h) f
  have hlim : ∫ ω, f ω ∂(pmOf μ : Measure ℝ) = ∫ y, f y ∂μ := rfl
  rw [hlim] at h2
  refine Tendsto.congr (fun N => ?_) h2
  rw [integral_empP, one_div]

theorem rank_lower {μ : Measure ℝ} [IsProbabilityMeasure μ] (hna : ∀ x, μ {x} = 0)
    {q : (N : ℕ) → Fin (N + 1) → ℝ} (hq : ∀ N, Monotone (q N)) (hw : EmpiricalWeakConv q μ)
    {i : (N : ℕ) → Fin (N + 1)} {α : ℝ}
    (hi : Tendsto (fun N : ℕ => (((i N : ℕ) : ℝ) + 1) / ((N : ℝ) + 1)) atTop (𝓝 α))
    {x : ℝ} (hx : μ.real (Iic x) < α) : ∀ᶠ N : ℕ in atTop, x < q N (i N) := by
  set μP : ProbabilityMeasure ℝ := pmOf μ with hμP
  have hw' := weakConv_tendsto hw
  have h0 : μP (frontier (Iic x)) = 0 := by
    rw [frontier_Iic]
    apply NNReal.eq
    rw [pm_real]
    simp [hμP, pmOf_coe, Measure.real, hna x]
  have h1 := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hw' h0
  have h2 := NNReal.tendsto_coe.2 h1
  have hlim : ((μP (Iic x) : ℝ≥0) : ℝ) = μ.real (Iic x) := by rw [pm_real, hμP, pmOf_coe]
  rw [hlim] at h2
  set θ := (μ.real (Iic x) + α) / 2 with hθ
  have e1 : ∀ᶠ N : ℕ in atTop, (((empP (q N)) (Iic x) : ℝ≥0) : ℝ) < θ :=
    h2.eventually (gt_mem_nhds (by rw [hθ]; linarith))
  have e2 : ∀ᶠ N : ℕ in atTop, θ < (((i N : ℕ) : ℝ) + 1) / ((N : ℝ) + 1) :=
    hi.eventually (lt_mem_nhds (by rw [hθ]; linarith))
  filter_upwards [e1, e2] with N h1N h2N
  by_contra hcon
  push Not at hcon
  rw [empP_apply _ measurableSet_Iic] at h1N
  have hc := mem_cnt (q N) (Iic x) (Finset.Iic (i N)) (fun j hj => by
    simp only [Finset.mem_Iic] at hj
    exact (hq N hj).trans hcon)
  rw [Fin.card_Iic] at hc
  have hc' : (((i N : ℕ) : ℝ) + 1) ≤ (cnt (q N) (Iic x) : ℝ) := by exact_mod_cast hc
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [lt_div_iff₀ hN] at h2N
  have h5 := (inv_mul_lt_iff₀ hN).1 h1N
  nlinarith

theorem rank_upper {μ : Measure ℝ} [IsProbabilityMeasure μ] (hna : ∀ x, μ {x} = 0)
    {q : (N : ℕ) → Fin (N + 1) → ℝ} (hq : ∀ N, Monotone (q N)) (hw : EmpiricalWeakConv q μ)
    {i : (N : ℕ) → Fin (N + 1)} {α : ℝ}
    (hi : Tendsto (fun N : ℕ => (((i N : ℕ) : ℝ) + 1) / ((N : ℝ) + 1)) atTop (𝓝 α))
    {y : ℝ} (hy : α < μ.real (Iio y)) : ∀ᶠ N : ℕ in atTop, q N (i N) < y := by
  set μP : ProbabilityMeasure ℝ := pmOf μ with hμP
  have hw' := weakConv_tendsto hw
  have h0 : μP (frontier (Iio y)) = 0 := by
    rw [frontier_Iio]
    apply NNReal.eq
    rw [pm_real]
    simp [hμP, pmOf_coe, Measure.real, hna y]
  have h1 := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hw' h0
  have h2 := NNReal.tendsto_coe.2 h1
  have hlim : ((μP (Iio y) : ℝ≥0) : ℝ) = μ.real (Iio y) := by rw [pm_real, hμP, pmOf_coe]
  rw [hlim] at h2
  have hi' : Tendsto (fun N : ℕ => ((i N : ℕ) : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 α) := by
    have h3 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      exact this
    have := hi.sub h3
    simp only [sub_zero] at this
    refine this.congr fun N => ?_
    field_simp
    ring
  set θ := (α + μ.real (Iio y)) / 2 with hθ
  have e1 : ∀ᶠ N : ℕ in atTop, θ < (((empP (q N)) (Iio y) : ℝ≥0) : ℝ) :=
    h2.eventually (lt_mem_nhds (by rw [hθ]; linarith))
  have e2 : ∀ᶠ N : ℕ in atTop, ((i N : ℕ) : ℝ) / ((N : ℝ) + 1) < θ :=
    hi'.eventually (gt_mem_nhds (by rw [hθ]; linarith))
  filter_upwards [e1, e2] with N h1N h2N
  by_contra hcon
  push Not at hcon
  rw [empP_apply _ measurableSet_Iio] at h1N
  have hc := cnt_le (q N) (Iio y) (Finset.Iio (i N)) (fun j hj => by
    simp only [Finset.mem_Iio]
    by_contra hh
    push Not at hh
    exact absurd (hcon.trans (hq N hh)) (not_le.2 hj))
  rw [Fin.card_Iio] at hc
  have hc' : (cnt (q N) (Iio y) : ℝ) ≤ ((i N : ℕ) : ℝ) := by exact_mod_cast hc
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h4 : ((N : ℝ) + 1)⁻¹ * (cnt (q N) (Iio y) : ℝ) ≤ ((i N : ℕ) : ℝ) / ((N : ℝ) + 1) := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hc' (by positivity)
  linarith

end QuantumNLS.F04SelRank
#print axioms QuantumNLS.F04SelRank.weakConv_tendsto
#print axioms QuantumNLS.F04SelRank.rank_lower
#print axioms QuantumNLS.F04SelRank.rank_upper
