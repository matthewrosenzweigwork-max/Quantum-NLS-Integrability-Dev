import Mathlib

/-! # H03 (v2 `C:cor:diagonal`), file a: the diagonal selection (Phi-free, probability-free)

v2 l.924-926: for every integer `k ≥ 2` choose a threshold `N_k ≥ k` such that for `N ≥ N_k` the
distances `ν_{k,N}` to `μ_k` are at most `1/k` on each of the finitely many spaces `H^r`, `r ≤ k-1`;
set `m(N) = max{k : N_k ≤ N}` with a fixed convention before `N_2`.

* `diagOrder38 Nk N = max 2 (greatest k ≤ N with 2 ≤ k ∧ Nk k ≤ N)`; the convention before `N_2`
  is the value `2` (H03.03).
* `diagOrder38_spec`, `le_diagOrder38`, `tendsto_diagOrder38` (H03.03, H03.04, `m(N) → ∞`).
* `exists_thresholds38` (H03.01, H03.02): thresholds `N_k ≥ k` from the finitely many spaces `r < k`.
* `diagonal_tendsto38` (H03.04, H03.05): the abstract diagonal argument.  For topological spaces
  `X r` with a metric inducing their topology, `ν r k N → μ r k` (`N → ∞`, each `r < k`) and
  `μ r k → L r` (`k → ∞`) give an explicit `m` with `m N → ∞`, `2 ≤ m N` and `ν r (m N) N → L r`
  for every `r`.  (The proof uses a metric only inside the proof: the statement is topological.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open Filter Topology

/-- **H03.03.** `m(N) = max{k ≥ 2 : N_k ≤ N}` (the largest threshold already reached), with the
value `2` as the fixed convention before `N_2`. -/
def diagOrder38 (Nk : ℕ → ℕ) (N : ℕ) : ℕ := by
  classical exact max 2 (Nat.findGreatest (fun k => 2 ≤ k ∧ Nk k ≤ N) N)

theorem two_le_diagOrder38 (Nk : ℕ → ℕ) (N : ℕ) : 2 ≤ diagOrder38 Nk N := by
  unfold diagOrder38
  exact le_max_left _ _

/-- For `N ≥ N_2` (with `N_k ≥ k`) the selected `m(N)` is a genuine threshold already reached. -/
theorem diagOrder38_spec (Nk : ℕ → ℕ) (hNk : ∀ k, k ≤ Nk k) (N : ℕ) (hN : Nk 2 ≤ N) :
    Nk (diagOrder38 Nk N) ≤ N := by
  classical
  have h2N : 2 ≤ N := (hNk 2).trans hN
  have hP := Nat.findGreatest_spec (P := fun k => 2 ≤ k ∧ Nk k ≤ N) h2N (⟨le_rfl, hN⟩ : 2 ≤ 2 ∧ Nk 2 ≤ N)
  have : diagOrder38 Nk N = Nat.findGreatest (fun k => 2 ≤ k ∧ Nk k ≤ N) N := by
    unfold diagOrder38
    exact max_eq_right hP.1
  rw [this]
  exact hP.2

/-- Every reached threshold bounds `m(N)` from below. -/
theorem le_diagOrder38 (Nk : ℕ → ℕ) (hNk : ∀ k, k ≤ Nk k) {K : ℕ} (hK : 2 ≤ K) (N : ℕ)
    (hN : Nk K ≤ N) : K ≤ diagOrder38 Nk N := by
  classical
  unfold diagOrder38
  refine le_trans ?_ (le_max_right _ _)
  exact Nat.le_findGreatest (P := fun k => 2 ≤ k ∧ Nk k ≤ N) ((hNk K).trans hN) ⟨hK, hN⟩

/-- **H03.04, part 1.** `m(N) → ∞`. -/
theorem tendsto_diagOrder38 (Nk : ℕ → ℕ) (hNk : ∀ k, k ≤ Nk k) :
    Tendsto (diagOrder38 Nk) atTop atTop := by
  refine tendsto_atTop.2 fun K => ?_
  refine eventually_atTop.2 ⟨Nk (max K 2), fun N hN => ?_⟩
  exact (le_max_left K 2).trans (le_diagOrder38 Nk hNk (le_max_right K 2) N hN)

section Thresholds

variable {X : ℕ → Type*} [∀ r, PseudoMetricSpace (X r)]

/-- **H03.01 / H03.02.** For each `k` there is a threshold `N_k ≥ k` such that for every `N ≥ N_k`
the distances on the finitely many spaces `r < k` are at most `1/(k+1)`. -/
theorem exists_thresholds38 (ν : ∀ r, ℕ → ℕ → X r) (μ : ∀ r, ℕ → X r)
    (h1 : ∀ r k, r < k → Tendsto (fun N => ν r k N) atTop (𝓝 (μ r k))) :
    ∃ Nk : ℕ → ℕ, (∀ k, k ≤ Nk k) ∧
      ∀ k N, Nk k ≤ N → ∀ r, r < k → dist (ν r k N) (μ r k) ≤ 1 / ((k : ℝ) + 1) := by
  have hk : ∀ k : ℕ, ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ r, r < k → dist (ν r k N) (μ r k) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hev : ∀ᶠ N in atTop, ∀ r ∈ Finset.range k, dist (ν r k N) (μ r k) < 1 / ((k : ℝ) + 1) := by
      rw [Filter.eventually_all_finset]
      intro r hr
      exact Metric.tendsto_nhds.1 (h1 r k (Finset.mem_range.1 hr)) _ hε
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
    exact ⟨N0, fun N hN r hr => (hN0 N hN r (Finset.mem_range.2 hr)).le⟩
  choose N0 hN0 using hk
  exact ⟨fun k => max (N0 k) k, fun k => le_max_right _ _,
    fun k N hN r hr => hN0 k N ((le_max_left _ _).trans hN) r hr⟩

end Thresholds

/-- **H03.04 / H03.05: the diagonal argument** (v2 l.924-926), explicit form.  Let `X r` be spaces
carrying a metric (`PseudoMetrizableSpace`: only the topology is used in the statement).  If
`ν r k N → μ r k` as `N → ∞` for every `r < k` and `μ r k → L r` as `k → ∞` for every `r`, then
there are thresholds `N_k ≥ k` such that `m = diagOrder38 N_•` (`m(N) = max{k ≥ 2 : N_k ≤ N}`)
satisfies `ν r (m N) N → L r` for every `r`. -/
theorem diagonal_tendsto_explicit38 {X : ℕ → Type*} [∀ r, TopologicalSpace (X r)]
    [∀ r, TopologicalSpace.PseudoMetrizableSpace (X r)]
    (ν : ∀ r, ℕ → ℕ → X r) (μ : ∀ r, ℕ → X r) (L : ∀ r, X r)
    (h1 : ∀ r k, r < k → Tendsto (fun N => ν r k N) atTop (𝓝 (μ r k)))
    (h2 : ∀ r, Tendsto (fun k => μ r k) atTop (𝓝 (L r))) :
    ∃ Nk : ℕ → ℕ, (∀ k, k ≤ Nk k) ∧
      ∀ r, Tendsto (fun N => ν r (diagOrder38 Nk N) N) atTop (𝓝 (L r)) := by
  let _ : ∀ r, PseudoMetricSpace (X r) := fun r =>
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric (X r)
  obtain ⟨Nk, hNk, hthr⟩ := exists_thresholds38 ν μ h1
  have hm : Tendsto (diagOrder38 Nk) atTop atTop := tendsto_diagOrder38 Nk hNk
  refine ⟨Nk, hNk, fun r => ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hdec : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hμ : Tendsto (fun N => dist (μ r (diagOrder38 Nk N)) (L r)) atTop (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero.1 (h2 r)).comp hm
  have hbound : Tendsto (fun N => 1 / (((diagOrder38 Nk N : ℕ) : ℝ) + 1) +
      dist (μ r (diagOrder38 Nk N)) (L r)) atTop (𝓝 0) := by
    simpa using (hdec.comp hm).add hμ
  refine squeeze_zero' (Eventually.of_forall fun N => dist_nonneg) ?_ hbound
  have hr : ∀ᶠ N in atTop, r < diagOrder38 Nk N := hm.eventually (eventually_gt_atTop r)
  filter_upwards [hr, eventually_ge_atTop (Nk 2)] with N hrN hN2
  calc dist (ν r (diagOrder38 Nk N) N) (L r)
      ≤ dist (ν r (diagOrder38 Nk N) N) (μ r (diagOrder38 Nk N)) +
          dist (μ r (diagOrder38 Nk N)) (L r) := dist_triangle _ _ _
    _ ≤ _ := by
      gcongr
      exact hthr _ N (diagOrder38_spec Nk hNk N hN2) r hrN

/-- Existential form: `m N → ∞`, `2 ≤ m N` and `ν r (m N) N → L r` for every `r`. -/
theorem diagonal_tendsto38 {X : ℕ → Type*} [∀ r, TopologicalSpace (X r)]
    [∀ r, TopologicalSpace.PseudoMetrizableSpace (X r)]
    (ν : ∀ r, ℕ → ℕ → X r) (μ : ∀ r, ℕ → X r) (L : ∀ r, X r)
    (h1 : ∀ r k, r < k → Tendsto (fun N => ν r k N) atTop (𝓝 (μ r k)))
    (h2 : ∀ r, Tendsto (fun k => μ r k) atTop (𝓝 (L r))) :
    ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧ (∀ N, 2 ≤ m N) ∧
      ∀ r, Tendsto (fun N => ν r (m N) N) atTop (𝓝 (L r)) := by
  obtain ⟨Nk, hNk, h⟩ := diagonal_tendsto_explicit38 ν μ L h1 h2
  exact ⟨diagOrder38 Nk, tendsto_diagOrder38 Nk hNk, two_le_diagOrder38 Nk, h⟩

end NlsGge.Birkhoff

end
