import QuantumNLS.EmpiricalRapidity

/-!
# DEF-011: convergence in probability for varying Born laws
(`definitions.tex`, `def:report-11`; `DEFINITIONS_LEDGER.md:225`)

> If `X_N` is defined on the `N`th Born space and `x` is deterministic in a metric space, `X_N → x` in
> probability means that for every `ε > 0` the probability of `d(X_N, x) > ε` tends to zero. The probability
> spaces need not be identified. Almost-sure subsequence arguments may use their product coupling; the
> probabilities being asserted are the original marginals.

Realized literally over an arbitrary family of probability spaces `(Ω N, P N)` indexed by `N`
(`TendstoInProbability`): `P_N{ω : ε < d(X_N ω, x)} → 0` for every `ε > 0`, the probabilities being those of the
original marginals `P N` (as values in `ℝ≥0∞`; no common space and no coupling are used).  The Born instance
(`BornInProbability`) takes `(Ω N, P N) = (𝓜_N, bornMeasure (Ψ N) u)` of the parametric DEF-007 and
DEF-010 (`EmpiricalRapidity.bornMeasure`), for any family of bases `Ψ N`; `TendstoInProbabilityWeak` is the
"weak-measure metric" version with values in probability measures on `ℝ` under the Lévy–Prokhorov metric
(`levyProkhorovDist`, mathlib's metrization of the weak topology).

Proved definitional/sanity facts: constants converge; limits are unique; the notion is stable under
continuous maps, sums, and under change of the underlying space when the laws agree
(`tendstoInProbability_comp_iff`: only the marginal laws matter); equivalent formulation
`P_N{d ≤ ε} → 1` (`tendstoInProbability_iff_compl`).  The product coupling is not constructed (it is used by the
source only inside proofs).
-/

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumNLS.BornConvergence

universe u v

section General

variable {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)] {E : Type v} [PseudoMetricSpace E]

/-- **Convergence in probability over varying probability spaces**: for every `ε > 0`,
`P_N(d(X_N, x) > ε) → 0`. -/
def TendstoInProbability (P : ∀ N, Measure (Ω N)) (X : ∀ N, Ω N → E) (x : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N => P N {ω | ε < dist (X N ω) x}) atTop (𝓝 0)

theorem tendstoInProbability_const (P : ∀ N, Measure (Ω N)) (x : E) :
    TendstoInProbability P (fun _ _ => x) x := by
  intro ε hε
  simp [hε.not_gt]

/-- Limits are unique (for probability spaces). -/
theorem TendstoInProbability.unique {F : Type v} [MetricSpace F] {P : ∀ N, Measure (Ω N)}
    [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, Ω N → F} {x y : F} (hx : TendstoInProbability P X x)
    (hy : TendstoInProbability P X y) : x = y := by
  by_contra hne
  have hd : 0 < dist x y := dist_pos.mpr hne
  set ε := dist x y / 3 with hε
  have hε0 : 0 < ε := by positivity
  have h1 := hx ε hε0
  have h2 := hy ε hε0
  have hsum := h1.add h2
  rw [add_zero] at hsum
  have hge : ∀ N, (1 : ℝ≥0∞) ≤ P N {ω | ε < dist (X N ω) x} + P N {ω | ε < dist (X N ω) y} := by
    intro N
    have hcov : (Set.univ : Set (Ω N)) ⊆
        {ω | ε < dist (X N ω) x} ∪ {ω | ε < dist (X N ω) y} := by
      intro ω _
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hcon
      have := dist_triangle_left x y (X N ω)
      linarith [hcon.1, hcon.2]
    calc (1 : ℝ≥0∞) = P N Set.univ := (measure_univ).symm
      _ ≤ P N ({ω | ε < dist (X N ω) x} ∪ {ω | ε < dist (X N ω) y}) := measure_mono hcov
      _ ≤ _ := measure_union_le _ _
  have hlim : (1 : ℝ≥0∞) ≤ 0 := ge_of_tendsto' hsum hge
  simp at hlim

/-- Stability under maps continuous at the limit. -/
theorem TendstoInProbability.comp_continuousAt {F : Type*} [PseudoMetricSpace F]
    {P : ∀ N, Measure (Ω N)} {X : ∀ N, Ω N → E} {x : E} (h : TendstoInProbability P X x)
    {g : E → F} (hg : ContinuousAt g x) :
    TendstoInProbability P (fun N ω => g (X N ω)) (g x) := by
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp hg ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h (δ / 2) (by positivity))
    (fun N => zero_le) (fun N => measure_mono ?_)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  have hle : dist (X N ω) x < δ := by linarith [not_lt.mp hcon]
  exact absurd (hδε hle) (not_lt.mpr hω.le)

/-- Sums of sequences converging in probability (same spaces). -/
theorem TendstoInProbability.add {G : Type*} [NormedAddCommGroup G]
    {P : ∀ N, Measure (Ω N)} {X Y : ∀ N, Ω N → G} {x y : G} (hX : TendstoInProbability P X x)
    (hY : TendstoInProbability P Y y) :
    TendstoInProbability P (fun N ω => X N ω + Y N ω) (x + y) := by
  intro ε hε
  have h1 := hX (ε / 2) (by positivity)
  have h2 := hY (ε / 2) (by positivity)
  have hs := h1.add h2
  rw [add_zero] at hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun N => zero_le) (fun N => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  have : dist (X N ω + Y N ω) (x + y) ≤ dist (X N ω) x + dist (Y N ω) y := dist_add_add_le _ _ _ _
  linarith [hcon.1, hcon.2]

/-- Equivalent formulation `P_N(d(X_N,x) ≤ ε) → 1`, for probability measures and measurable events. -/
theorem tendstoInProbability_iff_compl {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)]
    {X : ∀ N, Ω N → E} {x : E}
    (hmeas : ∀ N, Measurable fun ω => dist (X N ω) x) :
    TendstoInProbability P X x ↔
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N => P N {ω | dist (X N ω) x ≤ ε}) atTop (𝓝 1) := by
  have hc : ∀ N (ε : ℝ), P N {ω | dist (X N ω) x ≤ ε} = 1 - P N {ω | ε < dist (X N ω) x} := by
    intro N ε
    have hms : MeasurableSet {ω | ε < dist (X N ω) x} :=
      measurableSet_lt measurable_const (hmeas N)
    have := prob_compl_eq_one_sub (μ := P N) hms
    rw [← this]
    congr 1
    ext ω; simp
  constructor
  · intro h ε hε
    have e : (fun N => P N {ω | dist (X N ω) x ≤ ε}) =
        fun N => 1 - P N {ω | ε < dist (X N ω) x} := funext fun N => hc N ε
    rw [e]
    have := ENNReal.Tendsto.sub tendsto_const_nhds (h ε hε) (Or.inl ENNReal.one_ne_top)
    simpa using this
  · intro h ε hε
    have e : (fun N => P N {ω | dist (X N ω) x ≤ ε}) =
        fun N => 1 - P N {ω | ε < dist (X N ω) x} := funext fun N => hc N ε
    have h1 := h ε hε
    rw [e] at h1
    have hfin : (fun N => P N {ω | ε < dist (X N ω) x}) =
        fun N => 1 - (1 - P N {ω | ε < dist (X N ω) x}) := by
      funext N
      rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
    rw [hfin]
    have := ENNReal.Tendsto.sub tendsto_const_nhds h1 (Or.inl ENNReal.one_ne_top)
    simpa using this

end General

/-! ### Only the marginal laws matter -/

section Laws

variable {Ω Ω' : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)] [∀ N, MeasurableSpace (Ω' N)]
  {E : Type v} [PseudoMetricSpace E]

/-- If `P'_N` is the law of `f_N : Ω_N → Ω'_N` under `P_N`, then `X'_N ∘ f_N → x` in probability on the
spaces `(Ω_N, P_N)` iff `X'_N → x` in probability on `(Ω'_N, P'_N)` (for measurable events): the notion depends
only on the marginal laws, so the spaces need not be identified. -/
theorem tendstoInProbability_comp_iff (P : ∀ N, Measure (Ω N)) (f : ∀ N, Ω N → Ω' N)
    (hf : ∀ N, Measurable (f N)) (X' : ∀ N, Ω' N → E) (x : E)
    (hX : ∀ N (ε : ℝ), MeasurableSet {ω | ε < dist (X' N ω) x}) :
    TendstoInProbability P (fun N ω => X' N (f N ω)) x ↔
      TendstoInProbability (fun N => (P N).map (f N)) X' x := by
  have : ∀ N (ε : ℝ), P N {ω | ε < dist (X' N (f N ω)) x} =
      ((P N).map (f N)) {ω | ε < dist (X' N ω) x} := by
    intro N ε
    rw [Measure.map_apply (hf N) (hX N ε)]
    rfl
  unfold TendstoInProbability
  simp_rw [this]

end Laws

/-! ### The Born instances -/

section Born

open QuantumNLS.EmpiricalRapidity QuantumNLS.BetheCoefficientTransform
open QuantumNLS.PhysicalTensor

variable {L : ℝ} [Fact (0 < L)]

/-- Convergence in probability on the Born spaces `(𝓜_N, bornMeasure (Ψ N) u)` of a family of bases and a
unit profile `u` (the spaces are different for different `N` and are not identified). -/
def BornInProbability {E : Type v} [PseudoMetricSpace E] (Ψ : ∀ N, BetheBasis L N) (u : L2T L)
    (hu : ‖u‖ = 1) (X : ∀ N, QuantumNLS.BetheLabels.MArr N → E) (x : E) : Prop :=
  TendstoInProbability (fun N => bornMeasure (Ψ N) u hu) X x

/-- Convergence in probability in the weak-measure metric (Lévy–Prokhorov) of random probability measures on
`ℝ` to a deterministic probability measure. -/
def TendstoInProbabilityWeak {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    (ν : ∀ N, Ω N → MeasureTheory.ProbabilityMeasure ℝ) (μ : MeasureTheory.ProbabilityMeasure ℝ) : Prop :=
  TendstoInProbability P (fun N ω => LevyProkhorov.ofMeasure (ν N ω)) (LevyProkhorov.ofMeasure μ)

theorem tendstoInProbabilityWeak_iff {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) (ν : ∀ N, Ω N → MeasureTheory.ProbabilityMeasure ℝ)
    (μ : MeasureTheory.ProbabilityMeasure ℝ) :
    TendstoInProbabilityWeak P ν μ ↔ ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => P N {ω | ε < levyProkhorovDist (ν N ω).toMeasure μ.toMeasure})
        atTop (𝓝 0) := Iff.rfl

end Born

#print axioms TendstoInProbability.unique
#print axioms TendstoInProbability.add
#print axioms tendstoInProbability_iff_compl
#print axioms tendstoInProbability_comp_iff

end QuantumNLS.BornConvergence
