import Mathlib
import QuantumNLS.BornConvergence
import QuantumNLS.IndexedMasses

/-!
# DEF-012: rapidity transport distance and weighted action error

Source: `DEFINITIONS_LEDGER.md:247` (DEF-012), `chapters/definitions.tex`, `def:report-12`.  Ledger text: for a
fixed `p ≥ 1`, `W_p(μ,ν)` is the infimum of `(∫|x−y|^p dπ)^{1/p}` over couplings of probability measures, when their
`p`th moments are finite; for a nonnegative summable `A = (A_n)` and a fixed weight order `a ≥ 0`, the weighted
occupation error is `∑_n (1+|n|)^a |m_n/N − A_n|`, possibly infinite; the later application takes `A_n = a_n(u)` (the
DEF-014 indexed action); each asserted order is fixed before `N → ∞`; convergence in probability does not itself
imply convergence of untruncated moments.

## Transport distance
`IsCoupling π μ ν`, `cost p π = ∫⁻ ‖x−y‖ₑ^p dπ` (`‖t‖ₑ = ofReal |t|`), `moment p μ`, and
`wasserstein p μ ν = ⨅_{π coupling} (cost p π)^{1/p}` in `ℝ≥0∞` (`transportDist` its real value).  Proved:
* a coupling exists: the product (`isCoupling_prod`);
* finiteness: `wasserstein_lt_top` for `p ≥ 1` and finite `p`th moments (`cost_le`: every coupling has
  `∫|x−y|^p ≤ 2^{p−1}(m_p(μ)+m_p(ν))`);
* nonnegativity (`transportDist_nonneg`), `W_p(μ,μ) = 0` (`wasserstein_self`, diagonal coupling), symmetry
  (`wasserstein_comm`, swapped coupling).
The triangle inequality (gluing lemma) is **not** proved (optional in the task).

## Weighted occupation error
`weightedError a A N m = ∑' n, ofReal((1+|n|)^a |m_n/N − A_n|)` in `ℝ≥0∞` for `m ∈ 𝓜_N` (DEF-006's `MArr N`).
`weightedError_lt_top`: finite when `A ≥ 0` and `∑ (1+|n|)^a A_n < ∞` (otherwise it may be infinite, as the ledger
says); `weightedError_indexed_lt_top`: for `A = a_n` the DEF-014 indexed masses of a finite measure (`a = 0`).

## DEF-011 binding
`WeightedErrorInProbability P a A`: `P_N{ε < error} → 0` along marginals `P N` on `𝓜_N` (literal DEF-011 shape);
`weightedErrorInProbability_iff`: equivalent to the realized `BornConvergence.TendstoInProbability` of the
truncation `min 1 error`; `BornWeightedError` is the Born instance `(𝓜_N, bornMeasure (Ψ N) u)` (DEF-007/DEF-010) and
`BornWeightedErrorIndexed` the application `A_n = a_n(u)` via `IndexedMasses.indexedMassReal`.  No statement
asserts convergence of moments from convergence in probability.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.RapidityTransport

/-! ### Transport distance `W_p` -/

/-- `π` is a coupling of the probability measures `μ, ν` on `ℝ`: a probability measure on `ℝ × ℝ` with
marginals `μ` and `ν`. -/
structure IsCoupling (π : Measure (ℝ × ℝ)) (μ ν : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure π
  fst : π.map Prod.fst = μ
  snd : π.map Prod.snd = ν

/-- The `p`-th moment `∫ |x|^p dμ` (in `ℝ≥0∞`, `‖x‖ₑ = ofReal |x|`). -/
def moment (p : ℝ) (μ : Measure ℝ) : ℝ≥0∞ := ∫⁻ x, ‖x‖ₑ ^ p ∂μ

/-- The `p`-th moment is finite. -/
def HasFiniteMoment (p : ℝ) (μ : Measure ℝ) : Prop := moment p μ < ∞

/-- The transport cost `∫ |x − y|^p dπ` of a measure `π` on `ℝ × ℝ`. -/
def cost (p : ℝ) (π : Measure (ℝ × ℝ)) : ℝ≥0∞ := ∫⁻ z, ‖z.1 - z.2‖ₑ ^ p ∂π

/-- **DEF-012 transport distance** `W_p(μ,ν) = inf_π (∫|x−y|^p dπ)^{1/p}` over couplings `π` (value in
`ℝ≥0∞`; finite exactly when moments are finite, see `wasserstein_lt_top`). -/
def wasserstein (p : ℝ) (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (π : Measure (ℝ × ℝ)) (_ : IsCoupling π μ ν), cost p π ^ (1 / p)

/-- The real-valued distance (the ledger's `W_p` when the `p`th moments are finite). -/
def transportDist (p : ℝ) (μ ν : Measure ℝ) : ℝ := (wasserstein p μ ν).toReal

theorem enorm_sub_le' (a b : ℝ) : ‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  rw [sub_eq_add_neg]; exact (enorm_add_le _ _).trans (by rw [enorm_neg])

theorem enorm_sub_rev' (a b : ℝ) : ‖a - b‖ₑ = ‖b - a‖ₑ := by
  rw [← enorm_neg, neg_sub]

section Coupling

variable {μ ν : Measure ℝ}

/-- **A coupling exists: the product measure.** -/
theorem isCoupling_prod [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling (μ.prod ν) μ ν where
  prob := inferInstance
  fst := by simp [Measure.map_fst_prod]
  snd := by simp [Measure.map_snd_prod]

theorem hdiag : Measurable fun x : ℝ => (x, x) := by fun_prop

/-- The diagonal coupling of `μ` with itself. -/
theorem isCoupling_diag [IsProbabilityMeasure μ] :
    IsCoupling (μ.map fun x => (x, x)) μ μ where
  prob := inferInstance
  fst := by
    rw [Measure.map_map measurable_fst hdiag]
    exact Measure.map_id
  snd := by
    rw [Measure.map_map measurable_snd hdiag]
    exact Measure.map_id

/-- Swapping the coordinates turns a coupling of `(μ, ν)` into a coupling of `(ν, μ)`. -/
theorem IsCoupling.swap {π : Measure (ℝ × ℝ)} (h : IsCoupling π μ ν) :
    IsCoupling (π.map Prod.swap) ν μ := by
  have := h.prob
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst measurable_swap]; exact h.snd
  · rw [Measure.map_map measurable_snd measurable_swap]; exact h.fst

theorem cost_swap (p : ℝ) (π : Measure (ℝ × ℝ)) : cost p (π.map Prod.swap) = cost p π := by
  unfold cost
  rw [lintegral_map (by fun_prop) measurable_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  exact lintegral_congr fun z => by rw [enorm_sub_rev']

/-- Cost bound for every coupling: `∫|x−y|^p dπ ≤ 2^{p−1}(m_p(μ) + m_p(ν))`. -/
theorem cost_le {p : ℝ} (hp : 1 ≤ p) {π : Measure (ℝ × ℝ)} (h : IsCoupling π μ ν) :
    cost p π ≤ 2 ^ (p - 1) * (moment p μ + moment p ν) := by
  have hm1 : Measurable fun z : ℝ × ℝ => ‖z.1‖ₑ ^ p := (measurable_enorm.comp measurable_fst).pow_const p
  have hm2 : Measurable fun z : ℝ × ℝ => ‖z.2‖ₑ ^ p := (measurable_enorm.comp measurable_snd).pow_const p
  calc cost p π ≤ ∫⁻ z, 2 ^ (p - 1) * (‖z.1‖ₑ ^ p + ‖z.2‖ₑ ^ p) ∂π := by
        refine lintegral_mono fun z => ?_
        calc ‖z.1 - z.2‖ₑ ^ p ≤ (‖z.1‖ₑ + ‖z.2‖ₑ) ^ p :=
              ENNReal.rpow_le_rpow (enorm_sub_le' _ _) (by linarith)
          _ ≤ _ := ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
    _ = 2 ^ (p - 1) * (∫⁻ z, ‖z.1‖ₑ ^ p ∂π + ∫⁻ z, ‖z.2‖ₑ ^ p ∂π) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left hm1]
    _ = 2 ^ (p - 1) * (moment p μ + moment p ν) := by
        congr 2
        · rw [moment, ← h.fst, lintegral_map (measurable_enorm.pow_const p) measurable_fst]
        · rw [moment, ← h.snd, lintegral_map (measurable_enorm.pow_const p) measurable_snd]

end Coupling

section Properties

variable {μ ν : Measure ℝ}

theorem wasserstein_le_cost {p : ℝ} {π : Measure (ℝ × ℝ)} (h : IsCoupling π μ ν) :
    wasserstein p μ ν ≤ cost p π ^ (1 / p) :=
  iInf₂_le π h

/-- **`W_p` is finite when both `p`-th moments are finite** (`p ≥ 1`). -/
theorem wasserstein_lt_top [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {p : ℝ} (hp : 1 ≤ p)
    (hμ : HasFiniteMoment p μ) (hν : HasFiniteMoment p ν) : wasserstein p μ ν < ∞ := by
  refine lt_of_le_of_lt (wasserstein_le_cost (isCoupling_prod (μ := μ) (ν := ν))) ?_
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  refine ne_top_of_le_ne_top ?_ (cost_le hp isCoupling_prod)
  refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
    (ENNReal.add_ne_top.mpr ⟨hμ.ne, hν.ne⟩)

/-- `W_p ≥ 0` (real version). -/
theorem transportDist_nonneg (p : ℝ) (μ ν : Measure ℝ) : 0 ≤ transportDist p μ ν :=
  ENNReal.toReal_nonneg

/-- `W_p(μ,μ) = 0`. -/
theorem wasserstein_self [IsProbabilityMeasure μ] {p : ℝ} (hp : 0 < p) : wasserstein p μ μ = 0 := by
  refine le_antisymm ?_ bot_le
  refine (wasserstein_le_cost (isCoupling_diag (μ := μ))).trans (le_of_eq ?_)
  have : cost p (μ.map fun x => (x, x)) = 0 := by
    unfold cost
    rw [lintegral_map (by fun_prop) hdiag]
    simp [ENNReal.zero_rpow_of_pos hp]
  rw [this, ENNReal.zero_rpow_of_pos (by positivity)]

theorem transportDist_self [IsProbabilityMeasure μ] {p : ℝ} (hp : 0 < p) : transportDist p μ μ = 0 := by
  simp [transportDist, wasserstein_self hp]

theorem wasserstein_le_swap (p : ℝ) (μ ν : Measure ℝ) : wasserstein p μ ν ≤ wasserstein p ν μ := by
  refine le_iInf₂ fun π hπ => ?_
  refine le_trans (wasserstein_le_cost hπ.swap) (le_of_eq ?_)
  rw [cost_swap]

/-- **Symmetry**: `W_p(μ,ν) = W_p(ν,μ)`. -/
theorem wasserstein_comm (p : ℝ) (μ ν : Measure ℝ) : wasserstein p μ ν = wasserstein p ν μ :=
  le_antisymm (wasserstein_le_swap p μ ν) (wasserstein_le_swap p ν μ)

theorem transportDist_comm (p : ℝ) (μ ν : Measure ℝ) : transportDist p μ ν = transportDist p ν μ := by
  simp [transportDist, wasserstein_comm p μ ν]

end Properties


/-! ### Weighted occupation error -/

section Weighted

open QuantumNLS.BetheLabels (MArr)

/-- The weight `(1 + |n|)^a`. -/
def weight (a : ℝ) (n : ℤ) : ℝ := (1 + |(n : ℝ)|) ^ a

theorem weight_pos (a : ℝ) (n : ℤ) : 0 < weight a n :=
  Real.rpow_pos_of_pos (by positivity) a

/-- **DEF-012 weighted occupation error** `∑_n (1+|n|)^a |m_n/N − A_n|` (value in `ℝ≥0∞`: possibly
infinite), for a corrected-occupation array `m ∈ 𝓜_N` (DEF-006) and a sequence `A`. -/
def weightedError (a : ℝ) (A : ℤ → ℝ) (N : ℕ) (m : MArr N) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal (weight a n * |(m.1 n : ℝ) / N - A n|)

/-- The error is finite when `A ≥ 0` and `∑ (1+|n|)^a A_n < ∞` (`m` is finitely supported, so the
error may be infinite only through the tail of `A`). -/
theorem weightedError_lt_top (a : ℝ) {A : ℤ → ℝ} (hA0 : ∀ n, 0 ≤ A n)
    (hA : Summable fun n => weight a n * A n) (N : ℕ) (m : MArr N) :
    weightedError a A N m < ∞ := by
  have hle : weightedError a A N m ≤
      ∑' n : ℤ, ENNReal.ofReal (weight a n * ((m.1 n : ℝ) / N)) +
        ∑' n : ℤ, ENNReal.ofReal (weight a n * A n) := by
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun n => ?_
    rw [← ENNReal.ofReal_add (by have := weight_pos a n; positivity)
      (mul_nonneg (weight_pos a n).le (hA0 n))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (weight_pos a n).le
    have hx : 0 ≤ (m.1 n : ℝ) / N := by positivity
    rw [abs_le]; constructor <;> linarith [hA0 n]
  refine lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
  · rw [tsum_eq_sum (s := m.1.support)]
    · exact ENNReal.sum_lt_top.mpr fun n _ => ENNReal.ofReal_lt_top
    · intro n hn
      simp [Finsupp.notMem_support_iff.mp hn]
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (weight_pos a n).le (hA0 n)) hA]
    exact ENNReal.ofReal_lt_top

/-- Binding to the DEF-014 indexed masses `A_n = a_n(u)` (finite measure, `a = 0`, i.e. the `ℓ¹` error). -/
theorem weightedError_indexed_lt_top (P : QuantumNLS.IndexedMasses.BoundaryPhase) (M : Measure ℝ)
    [IsFiniteMeasure M] (N : ℕ) (m : MArr N) :
    weightedError 0 (P.indexedMassReal M) N m < ∞ := by
  refine weightedError_lt_top 0 (fun n => ENNReal.toReal_nonneg) ?_ N m
  have h := P.summable_indexedMassReal M
  unfold QuantumNLS.IndexedMasses.BoundaryPhase.indexedMassReal at h
  simpa [weight] using h

/-- **DEF-011 binding.**  `weightedError a A N → 0` in probability along the marginals `P N` on `𝓜_N`
(`P_N{ε < error} → 0`; no moment convergence is asserted). -/
def WeightedErrorInProbability (P : ∀ N, Measure (MArr N)) (a : ℝ) (A : ℤ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N => P N {m | ENNReal.ofReal ε < weightedError a A N m}) atTop (𝓝 0)

/-- The error truncated at `1`, a real random variable (so the realized DEF-011
`BornConvergence.TendstoInProbability` applies). -/
def truncatedError (a : ℝ) (A : ℤ → ℝ) (N : ℕ) (m : MArr N) : ℝ :=
  (min 1 (weightedError a A N m)).toReal

theorem lt_toReal_min_iff {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (e : ℝ≥0∞) :
    ε < (min 1 e).toReal ↔ ENNReal.ofReal ε < e := by
  rw [← ENNReal.ofReal_lt_iff_lt_toReal h0.le (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)),
    lt_min_iff]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by rwa [ENNReal.ofReal_lt_one], h⟩

/-- The error converges to `0` in probability iff its truncation does, in the realized DEF-011 sense. -/
theorem weightedErrorInProbability_iff (P : ∀ N, Measure (MArr N)) (a : ℝ) (A : ℤ → ℝ) :
    WeightedErrorInProbability P a A ↔
      QuantumNLS.BornConvergence.TendstoInProbability P (fun N m => truncatedError a A N m) 0 := by
  have hset : ∀ N (ε : ℝ), 0 < ε → ε < 1 →
      {m : MArr N | ε < dist (truncatedError a A N m) 0} = {m | ENNReal.ofReal ε < weightedError a A N m} := by
    intro N ε h0 h1
    ext m
    simp only [Set.mem_setOf_eq, truncatedError, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg]
    exact lt_toReal_min_iff h0 h1 _
  constructor
  · intro h ε hε
    by_cases h1 : ε < 1
    · simp only [hset _ ε hε h1]; exact h ε hε
    · have : ∀ N, {m : MArr N | ε < dist (truncatedError a A N m) 0} = ∅ := by
        intro N; ext m
        simp only [Set.mem_setOf_eq, truncatedError, dist_zero_right, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg, Set.mem_empty_iff_false, iff_false, not_lt]
        have : (min 1 (weightedError a A N m)).toReal ≤ 1 :=
          (ENNReal.toReal_mono ENNReal.one_ne_top (min_le_left _ _)).trans (by simp)
        linarith [not_lt.mp h1]
      have hz : ∀ N, P N {m : MArr N | ε < dist (truncatedError a A N m) 0} = 0 := fun N => by
        rw [this N]; simp
      exact (tendsto_congr hz).mpr tendsto_const_nhds
  · intro h ε hε
    set ε' : ℝ := min ε (1 / 2) with hε'
    have h0 : 0 < ε' := lt_min hε (by norm_num)
    have h1 : ε' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have h2 := h ε' h0
    simp only [hset _ ε' h0 h1] at h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun N => bot_le)
      (fun N => measure_mono fun m hm => ?_)
    simp only [Set.mem_setOf_eq] at hm ⊢
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (min_le_left _ _)) hm

open QuantumNLS.PhysicalTensor in
/-- The Born-law instance: `(𝓜_N, bornMeasure (Ψ N) u)` of DEF-007/DEF-010. -/
def BornWeightedError {L : ℝ} [Fact (0 < L)] (Ψ : ∀ N, QuantumNLS.BetheCoefficientTransform.BetheBasis L N)
    (u : L2T L) (hu : ‖u‖ = 1) (a : ℝ) (A : ℤ → ℝ) : Prop :=
  WeightedErrorInProbability (fun N => QuantumNLS.EmpiricalRapidity.bornMeasure (Ψ N) u hu) a A

open QuantumNLS.PhysicalTensor in
theorem bornWeightedError_iff {L : ℝ} [Fact (0 < L)]
    (Ψ : ∀ N, QuantumNLS.BetheCoefficientTransform.BetheBasis L N) (u : L2T L) (hu : ‖u‖ = 1)
    (a : ℝ) (A : ℤ → ℝ) :
    BornWeightedError Ψ u hu a A ↔
      QuantumNLS.BornConvergence.BornInProbability Ψ u hu (fun N m => truncatedError a A N m) 0 :=
  weightedErrorInProbability_iff _ a A

open QuantumNLS.PhysicalTensor in
/-- The later application of DEF-012: `A_n = a_n(u)`, the DEF-014 indexed mass of a finite measure `M`
(= `M_{κ,u}`) with boundary phase `P`. -/
def BornWeightedErrorIndexed {L : ℝ} [Fact (0 < L)]
    (Ψ : ∀ N, QuantumNLS.BetheCoefficientTransform.BetheBasis L N) (u : L2T L) (hu : ‖u‖ = 1) (a : ℝ)
    (P : QuantumNLS.IndexedMasses.BoundaryPhase) (M : Measure ℝ) : Prop :=
  BornWeightedError Ψ u hu a (P.indexedMassReal M)

end Weighted

end QuantumNLS.RapidityTransport

#print axioms QuantumNLS.RapidityTransport.isCoupling_prod
#print axioms QuantumNLS.RapidityTransport.cost_le
#print axioms QuantumNLS.RapidityTransport.wasserstein_lt_top
#print axioms QuantumNLS.RapidityTransport.wasserstein_self
#print axioms QuantumNLS.RapidityTransport.wasserstein_comm
#print axioms QuantumNLS.RapidityTransport.weightedError_lt_top
#print axioms QuantumNLS.RapidityTransport.weightedError_indexed_lt_top
#print axioms QuantumNLS.RapidityTransport.weightedErrorInProbability_iff
#print axioms QuantumNLS.RapidityTransport.bornWeightedError_iff
