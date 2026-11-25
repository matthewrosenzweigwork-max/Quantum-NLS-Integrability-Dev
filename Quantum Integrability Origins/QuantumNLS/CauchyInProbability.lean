import Mathlib
import QuantumNLS.CauchyLimitCriterion
import QuantumNLS.BornConvergence

/-!
# From convergence in probability of Cauchy transforms to weak convergence in probability

Source use: `ROOT_spectral_measure.tex`, `thm:root-measure`, Step 5 ("weak convergence in probability").  The printed argument extracts
almost surely convergent subsequences on a product of the countable Born spaces; convergence in probability does not depend on the
coupling.  Here no coupling is constructed: a deterministic selection of outcomes (`select`) plays the role of the almost-sure
subsequence, and the subsequence criterion is replaced by a contradiction argument along a subsequence of indices.

Abstract theorem `exists_weak_limit_in_probability`: let `(Ω_N, P_N)` be probability spaces and `ν_N : Ω_N → ProbabilityMeasure ℝ` random
probability measures.  Let `g : ℂ → ℂ`, a point `η₀ > 0`, a dense sequence `q_k` of reals and heights `Y_j > 0`.  Assume

* (no loss of mass) `1 + Y_j Im g(iY_j) → 0`;
* (concentration) for every `z` among the line points `q_k + iη₀` and the points `iY_j`, every `δ > 0`:
  `P_N(‖G_{ν_N}(z) − g(z)‖ ≥ δ) → 0`.

Then there is a probability measure `μ` with `G_μ(q_k + iη₀) = g(q_k + iη₀)` for all `k` (unique, by `CauchyUniqueness`) and
`ν_N → μ` weakly in probability (`BornConvergence.TendstoInProbabilityWeak`, Lévy-Prokhorov metric).

No EXT-025 contract is used: compactness is mathlib's Prokhorov theorem applied to tight sequences (`CauchyLimitCriterion`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumNLS.CauchyInProbability

open QuantumNLS.CauchyUniqueness (cauchyTransform)
open QuantumNLS.CauchyLimitCriterion (exists_limit tendsto_of_cauchy)
open QuantumNLS.BornConvergence (TendstoInProbabilityWeak tendstoInProbabilityWeak_iff)

/-! ### Selection of outcomes -/

/-- **Selection**: if the sets `Good N n` are eventually (in `N`) nonempty for each `n`, there are outcomes `ω N ∈ Good N (nn N)` for all
large `N`, with `nn N → ∞`. -/
theorem select {Ω : ℕ → Type*} [∀ N, Nonempty (Ω N)] (Good : ∀ N, ℕ → Set (Ω N))
    (hev : ∀ n, ∀ᶠ N in atTop, (Good N n).Nonempty) :
    ∃ (ω : ∀ N, Ω N) (nn : ℕ → ℕ), Tendsto nn atTop atTop ∧ ∀ᶠ N in atTop, ω N ∈ Good N (nn N) := by
  classical
  let nn : ℕ → ℕ := fun N => Nat.findGreatest (fun n => (Good N n).Nonempty) N
  refine ⟨fun N => if h : (Good N (nn N)).Nonempty then h.some else Classical.arbitrary _, nn, ?_, ?_⟩
  · rw [tendsto_atTop]
    intro n
    filter_upwards [hev n, eventually_ge_atTop n] with N hN hnN
    exact Nat.le_findGreatest hnN hN
  · filter_upwards [hev 0] with N hN
    have hnn : (Good N (nn N)).Nonempty :=
      Nat.findGreatest_spec (P := fun n => (Good N n).Nonempty) (Nat.zero_le N) hN
    simp only [dif_pos hnn]
    exact hnn.some_mem

/-! ### Finite configurations of Cauchy values -/

/-- The finite configuration event: the first `n+1` line values and heights agree with `g` within `1/(n+1)`. -/
def Cfg (g : ℂ → ℂ) (Z W : ℕ → ℂ) {α : Type*} (ν : α → ProbabilityMeasure ℝ) (n : ℕ) : Set α :=
  {ω | ∀ k ≤ n, ‖cauchyTransform (ν ω : Measure ℝ) (Z k) - g (Z k)‖ < 1 / ((n : ℝ) + 1) ∧
      ‖cauchyTransform (ν ω : Measure ℝ) (W k) - g (W k)‖ < 1 / ((n : ℝ) + 1)}

theorem tendsto_of_good {f : ℕ → ℂ} {a : ℂ} {nn : ℕ → ℕ} (hnn : Tendsto nn atTop atTop) (k : ℕ)
    (h : ∀ᶠ N in atTop, k ≤ nn N → ‖f N - a‖ < 1 / ((nn N : ℝ) + 1)) : Tendsto f atTop (𝓝 a) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hε
  filter_upwards [h, hnn.eventually_ge_atTop (max k n₀)] with N hN hge
  have hk : k ≤ nn N := (le_max_left _ _).trans hge
  have hn : n₀ ≤ nn N := (le_max_right _ _).trans hge
  rw [dist_eq_norm]
  refine (hN hk).trans_le ?_
  refine le_trans ?_ hn₀.le
  gcongr

theorem good_converges {g : ℂ → ℂ} {Z W : ℕ → ℂ} {α : ℕ → Type*} (ν : ∀ j, α j → ProbabilityMeasure ℝ)
    (ω : ∀ j, α j) (nn : ℕ → ℕ) (hnn : Tendsto nn atTop atTop)
    (hω : ∀ᶠ j in atTop, ω j ∈ Cfg g Z W (ν j) (nn j)) (k : ℕ) :
    Tendsto (fun j => cauchyTransform (ν j (ω j) : Measure ℝ) (Z k)) atTop (𝓝 (g (Z k))) ∧
    Tendsto (fun j => cauchyTransform (ν j (ω j) : Measure ℝ) (W k)) atTop (𝓝 (g (W k))) := by
  constructor
  · refine tendsto_of_good hnn k ?_
    filter_upwards [hω] with j hj hk
    exact (hj k hk).1
  · refine tendsto_of_good hnn k ?_
    filter_upwards [hω] with j hj hk
    exact (hj k hk).2

section Prob

universe u

variable {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
  [∀ N, IsProbabilityMeasure (P N)] (ν : ∀ N, Ω N → ProbabilityMeasure ℝ)
  {g : ℂ → ℂ} {Z W : ℕ → ℂ}

theorem cfg_prob
    (hZ : ∀ k, ∀ δ : ℝ, 0 < δ → Tendsto
      (fun N => P N {ω | δ ≤ ‖cauchyTransform (ν N ω : Measure ℝ) (Z k) - g (Z k)‖}) atTop (𝓝 0))
    (hW : ∀ k, ∀ δ : ℝ, 0 < δ → Tendsto
      (fun N => P N {ω | δ ≤ ‖cauchyTransform (ν N ω : Measure ℝ) (W k) - g (W k)‖}) atTop (𝓝 0))
    (n : ℕ) : Tendsto (fun N => P N (Cfg g Z W (ν N) n)ᶜ) atTop (𝓝 0) := by
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hsum : Tendsto (fun N => ∑ k ∈ Finset.range (n + 1),
      (P N {ω | 1 / ((n : ℝ) + 1) ≤ ‖cauchyTransform (ν N ω : Measure ℝ) (Z k) - g (Z k)‖} +
        P N {ω | 1 / ((n : ℝ) + 1) ≤ ‖cauchyTransform (ν N ω : Measure ℝ) (W k) - g (W k)‖})) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range (n + 1)) (fun k _ => (hZ k _ hδ).add (hW k _ hδ))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun N => zero_le) (fun N => ?_)
  calc P N (Cfg g Z W (ν N) n)ᶜ
      ≤ P N (⋃ k ∈ Finset.range (n + 1),
          ({ω | 1 / ((n : ℝ) + 1) ≤ ‖cauchyTransform (ν N ω : Measure ℝ) (Z k) - g (Z k)‖} ∪
            {ω | 1 / ((n : ℝ) + 1) ≤ ‖cauchyTransform (ν N ω : Measure ℝ) (W k) - g (W k)‖})) := by
        refine measure_mono ?_
        intro ω hω
        simp only [Cfg, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hω
        obtain ⟨k, hk, hk2⟩ := hω
        simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq, Finset.mem_range]
        refine ⟨k, Nat.lt_succ_of_le hk, ?_⟩
        by_contra hcon
        push Not at hcon
        exact hk2 ⟨hcon.1, hcon.2⟩
    _ ≤ ∑ k ∈ Finset.range (n + 1), P N
          ({ω | 1 / ((n : ℝ) + 1) ≤ ‖cauchyTransform (ν N ω : Measure ℝ) (Z k) - g (Z k)‖} ∪
            {ω | 1 / ((n : ℝ) + 1) ≤ ‖cauchyTransform (ν N ω : Measure ℝ) (W k) - g (W k)‖}) :=
        measure_biUnion_finset_le _ _
    _ ≤ _ := Finset.sum_le_sum fun k _ => measure_union_le _ _

theorem cfg_eventually_nonempty
    (hZ : ∀ k, ∀ δ : ℝ, 0 < δ → Tendsto
      (fun N => P N {ω | δ ≤ ‖cauchyTransform (ν N ω : Measure ℝ) (Z k) - g (Z k)‖}) atTop (𝓝 0))
    (hW : ∀ k, ∀ δ : ℝ, 0 < δ → Tendsto
      (fun N => P N {ω | δ ≤ ‖cauchyTransform (ν N ω : Measure ℝ) (W k) - g (W k)‖}) atTop (𝓝 0))
    (n : ℕ) : ∀ᶠ N in atTop, (Cfg g Z W (ν N) n).Nonempty := by
  filter_upwards [(cfg_prob P ν hZ hW n).eventually (gt_mem_nhds zero_lt_one)] with N hN
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  rw [hempty, Set.compl_empty, measure_univ] at hN
  exact lt_irrefl _ hN

theorem nonempty_of_prob {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    Nonempty α := by
  have : (Set.univ : Set α).Nonempty :=
    nonempty_of_measure_ne_zero (μ := μ) (s := Set.univ) (by simp)
  exact this.to_type

/-- **Abstract theorem**: concentration of the Cauchy transforms at countably many points, together with no loss of mass, give a probability
measure `μ` (with `G_μ = g` on the line points) such that `ν_N → μ` weakly in probability. -/
theorem exists_weak_limit_in_probability {η₀ : ℝ} {q : ℕ → ℝ} {Y : ℕ → ℝ}
    (hη : 0 < η₀) (hq : DenseRange q) (hY : ∀ j, 0 < Y j)
    (hZdef : ∀ k, Z k = (q k : ℂ) + η₀ * Complex.I) (hWdef : ∀ j, W j = Complex.I * (Y j : ℂ))
    (hmass : Tendsto (fun j => 1 + Y j * (g (W j)).im) atTop (𝓝 0))
    (hZ : ∀ k, ∀ δ : ℝ, 0 < δ → Tendsto
      (fun N => P N {ω | δ ≤ ‖cauchyTransform (ν N ω : Measure ℝ) (Z k) - g (Z k)‖}) atTop (𝓝 0))
    (hW : ∀ k, ∀ δ : ℝ, 0 < δ → Tendsto
      (fun N => P N {ω | δ ≤ ‖cauchyTransform (ν N ω : Measure ℝ) (W k) - g (W k)‖}) atTop (𝓝 0)) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ k, cauchyTransform (μ : Measure ℝ) (Z k) = g (Z k)) ∧ TendstoInProbabilityWeak P ν μ := by
  haveI : ∀ N, Nonempty (Ω N) := fun N => nonempty_of_prob (P N)
  -- Step A: a deterministic selection of outcomes whose Cauchy values converge
  obtain ⟨ω, nn, hnn, hω⟩ := select (fun N n => Cfg g Z W (ν N) n) (cfg_eventually_nonempty P ν hZ hW)
  have hconv := fun k => good_converges (g := g) (Z := Z) (W := W) (fun N => ν N) ω nn hnn hω k
  have hmass' : Tendsto (fun j => 1 + Y j * (g (Complex.I * (Y j : ℂ))).im) atTop (𝓝 0) := by
    simpa [hWdef] using hmass
  obtain ⟨μ, hμ⟩ := exists_limit (η₀ := η₀) (q := q) (g := g) (Y := Y) hη (fun N => ν N (ω N)) hY hmass'
    (fun j => by simpa [hWdef] using (hconv j).2)
    (fun k => by simpa [hZdef] using (hconv k).1)
  have hμZ : ∀ k, cauchyTransform (μ : Measure ℝ) (Z k) = g (Z k) := fun k => by
    simpa [hZdef] using hμ k
  refine ⟨μ, hμZ, ?_⟩
  -- Step B: convergence in probability, by contradiction along a subsequence
  rw [tendstoInProbabilityWeak_iff]
  intro ε hε
  by_contra hnot
  rw [ENNReal.tendsto_nhds_zero] at hnot
  push Not at hnot
  obtain ⟨δ, hδ, hfreq⟩ := hnot
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  let Bad : ∀ j, Set (Ω (φ j)) := fun j => {ω | ε < levyProkhorovDist (ν (φ j) ω).toMeasure μ.toMeasure}
  have hev : ∀ n, ∀ᶠ j in atTop, (Cfg g Z W (ν (φ j)) n ∩ Bad j).Nonempty := by
    intro n
    have h1 := (cfg_prob P ν hZ hW n).comp hφ.tendsto_atTop
    filter_upwards [h1.eventually (gt_mem_nhds hδ)] with j hj
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hsub : Bad j ⊆ (Cfg g Z W (ν (φ j)) n)ᶜ := by
      intro ω hωB hωC
      have : ω ∈ Cfg g Z W (ν (φ j)) n ∩ Bad j := ⟨hωC, hωB⟩
      rw [hempty] at this
      exact this
    have := measure_mono (μ := P (φ j)) hsub
    exact absurd (lt_of_lt_of_le (hφP j) this) (not_lt.2 hj.le)
  haveI : ∀ j, Nonempty (Ω (φ j)) := fun j => nonempty_of_prob (P (φ j))
  obtain ⟨ω', nn', hnn', hω'⟩ := select (fun j n => Cfg g Z W (ν (φ j)) n ∩ Bad j) hev
  have hconv' := fun k => good_converges (g := g) (Z := Z) (W := W) (fun j => ν (φ j)) ω' nn' hnn'
    (hω'.mono fun j hj => hj.1) k
  have hlim : Tendsto (fun j => ν (φ j) (ω' j)) atTop (𝓝 μ) :=
    QuantumNLS.CauchyLimitCriterion.tendsto_of_cauchy (η₀ := η₀) (q := q) (g := g) (Y := Y) hη hq _ hY μ
      (fun k => by simpa [hZdef] using hμZ k) hmass'
      (fun j => by simpa [hWdef] using (hconv' j).2)
      (fun k => by simpa [hZdef] using (hconv' k).1)
  have hd := tendsto_iff_dist_tendsto_zero.1
    ((LevyProkhorov.probabilityMeasureHomeomorph.continuous.tendsto μ).comp hlim)
  have hd' : Tendsto (fun j => levyProkhorovDist (ν (φ j) (ω' j)).toMeasure μ.toMeasure) atTop (𝓝 0) := hd
  obtain ⟨j, hj1, hj2⟩ := ((hd'.eventually (gt_mem_nhds hε)).and (hω'.mono fun j hj => hj.2)).exists
  exact absurd hj1 (not_lt.2 hj2.le)

end Prob

end QuantumNLS.CauchyInProbability

#print axioms QuantumNLS.CauchyInProbability.select
#print axioms QuantumNLS.CauchyInProbability.good_converges
#print axioms QuantumNLS.CauchyInProbability.cfg_prob
#print axioms QuantumNLS.CauchyInProbability.exists_weak_limit_in_probability
