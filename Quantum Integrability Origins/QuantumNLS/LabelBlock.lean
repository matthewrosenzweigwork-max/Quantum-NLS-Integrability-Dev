import QuantumNLS.LabelExactSeparation

/-!
# PROP-004 `cor:B3-label-block` (label_periods.tex:226-252)

Source statement. Fix an integer `n` and two real cutpoints `x₋ < x₊` outside `supp μ`, satisfying
`2π(n−1) < F(x₋) < 2πn` and `2πn < F(x₊) < 2π(n+1)`. Under the hypotheses of
`thm:B3-exact-separation`, for every sufficiently large `N`, `x₋ < q_j < x₊ ⇔ n_j = n`. Both vertical
lines through the cutpoints have a fixed positive distance from all roots. The conclusions are uniform
on any family whose empirical measures converge weakly to `μ` uniformly. For a random on-shell
configuration with empirical measure converging weakly in probability to `μ`, they hold with
probability tending to one. No positive lower bound on the action of label `n` is required.

Realization (on PROP-003, XS2 `LabelExactSeparation` `0058fbfb…`, own, read-only): cutpoints are
DEF-043 regular cuts (`x± ∈ S.cuts ⊆ (supp μ)ᶜ`, as in PROP-003), `F = exteriorForce L κ S.μ`.
* **`label_block_uniform`**: `δ > 0`, a weak neighbourhood `U` of `μ` and `N₀` such that every on-shell
  configuration with `N ≥ N₀` and `L_N ∈ U` satisfies the block identification and stays `δ` away
  from both cutpoints (printed proof: apply the theorem with thresholds `n−1` and `n`, intersect);
* **`label_block_seq`**: along any sequence with `L_{N_k} ⇀ μ`, `N_k → ∞`, eventually;
* **`label_block_prob`**: for random on-shell configurations whose empirical measures converge weakly
  in probability to `μ` (for every weak neighbourhood `U`, `P(L_N ∉ U) → 0`), the conclusion holds with
  probability tending to one (the event is not assumed measurable; `P` is applied as an outer
  measure). The printed proof passes through a.s.-convergent subsequences; here the uniform form gives
  the same conclusion directly.
No hypothesis on the action of label `n` occurs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set

namespace QuantumNLS.LabelBlock

open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelExactSeparation
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts

/-- The block conclusion for one configuration. -/
def BlockConclusion {L κ : ℝ} {N : ℕ} (B : OnShellBethe L κ N) (n : ℤ) (xm xp δ : ℝ) : Prop :=
  ∀ j, ((xm < B.q j ∧ B.q j < xp) ↔ B.n j = n) ∧ δ ≤ |B.q j - xm| ∧ δ ≤ |B.q j - xp|

/-- Intersection of the two separation conclusions. -/
lemma block_of_cuts {L κ : ℝ} {N : ℕ} (B : OnShellBethe L κ N) {n : ℤ} {xm xp δ₁ δ₂ : ℝ}
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hm : ∀ j, (B.n j ≤ n - 1 → B.q j < xm - δ₁) ∧ (n - 1 + 1 ≤ B.n j → xm + δ₁ < B.q j))
    (hp : ∀ j, (B.n j ≤ n → B.q j < xp - δ₂) ∧ (n + 1 ≤ B.n j → xp + δ₂ < B.q j)) :
    BlockConclusion B n xm xp (min δ₁ δ₂) := by
  intro j
  have hd1 := min_le_left δ₁ δ₂
  have hd2 := min_le_right δ₁ δ₂
  refine ⟨⟨fun ⟨h1, h2⟩ => ?_, fun h => ?_⟩, ?_, ?_⟩
  · by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := (hm j).1 (by omega); linarith
    · have := (hp j).2 (by omega); linarith
  · exact ⟨by have := (hm j).2 (by omega); linarith, by have := (hp j).1 (by omega); linarith⟩
  · by_cases h : B.n j ≤ n - 1
    · have := (hm j).1 h
      rw [abs_of_neg (by linarith)]; linarith
    · have := (hm j).2 (by omega)
      rw [abs_of_pos (by linarith)]; linarith
  · by_cases h : B.n j ≤ n
    · have := (hp j).1 h
      rw [abs_of_neg (by linarith)]; linarith
    · have := (hp j).2 (by omega)
      rw [abs_of_pos (by linarith)]; linarith

/-- **PROP-004, uniform form.** -/
theorem label_block_uniform {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {n : ℤ} {xm xp : ℝ}
    (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (_hlt : xm < xp)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ δ > 0, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U → BlockConclusion B n xm xp δ := by
  obtain ⟨δ₁, hδ₁, U₁, hU₁, N₁, hN₁⟩ := exact_separation_uniform S hμ hxm (a := n - 1)
    (by push_cast; linarith) (by push_cast; linarith)
  obtain ⟨δ₂, hδ₂, U₂, hU₂, N₂, hN₂⟩ := exact_separation_uniform S hμ hxp (a := n) h3 h4
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, U₁ ∩ U₂, inter_mem hU₁ hU₂, max N₁ N₂,
    fun N hN hNN B hB => ?_⟩
  exact block_of_cuts B hδ₁ hδ₂ (hN₁ N hN (le_of_max_le_left hNN) B hB.1)
    (hN₂ N hN (le_of_max_le_right hNN) B hB.2)

/-- **PROP-004 along a sequence.** -/
theorem label_block_seq {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
    {B : ∀ k, OnShellBethe L κ (N k)}
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
    {n : ℤ} {xm xp : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ δ > 0, ∀ᶠ k in atTop, BlockConclusion (B k) n xm xp δ := by
  obtain ⟨δ, hδ, U, hU, N₀, hN₀⟩ := label_block_uniform S hμ hxm hxp hlt h1 h2 h3 h4
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hconv.eventually (mem_of_superset hU subset_rfl),
    hNtop.eventually (eventually_ge_atTop N₀)] with k hk1 hk2
  exact hN₀ (N k) (hN k) hk2 (B k) hk1

/-- **PROP-004, probabilistic form**: random on-shell configurations whose root empirical measures
converge weakly in probability to `μ` satisfy the block conclusion with probability tending to one. -/
theorem label_block_prob {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} (hNtop : Tendsto N atTop atTop)
    {B : ∀ k, Ω → OnShellBethe L κ (N k)}
    (hprob : ∀ U ∈ 𝓝 μ, Tendsto (fun k => P {ω | rootP (B k ω) (hN k) ∉ U}) atTop (𝓝 0))
    {n : ℤ} {xm xp : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ δ > 0, Tendsto (fun k => P {ω | BlockConclusion (B k ω) n xm xp δ}) atTop (𝓝 1) := by
  obtain ⟨δ, hδ, U, hU, N₀, hN₀⟩ := label_block_uniform S hμ hxm hxp hlt h1 h2 h3 h4
  refine ⟨δ, hδ, ?_⟩
  have hbad := hprob U hU
  -- `P(bad) ≤ P(L_N ∉ U)` eventually, and `1 − P(bad) ≤ P(good) ≤ 1`
  have hsub : ∀ᶠ k in atTop, {ω | BlockConclusion (B k ω) n xm xp δ}ᶜ ⊆
      {ω | rootP (B k ω) (hN k) ∉ U} := by
    filter_upwards [hNtop.eventually (eventually_ge_atTop N₀)] with k hk
    intro ω hω hin
    exact hω (hN₀ (N k) (hN k) hk (B k ω) hin)
  have hlow : ∀ᶠ k in atTop, 1 - P {ω | rootP (B k ω) (hN k) ∉ U} ≤
      P {ω | BlockConclusion (B k ω) n xm xp δ} := by
    filter_upwards [hsub] with k hk
    have h1' := measure_univ_le_add_compl (μ := P) {ω | BlockConclusion (B k ω) n xm xp δ}
    rw [measure_univ] at h1'
    have h2' := measure_mono (μ := P) hk
    calc 1 - P {ω | rootP (B k ω) (hN k) ∉ U}
        ≤ 1 - P {ω | BlockConclusion (B k ω) n xm xp δ}ᶜ := tsub_le_tsub_left h2' 1
      _ ≤ P {ω | BlockConclusion (B k ω) n xm xp δ} := tsub_le_iff_right.2 h1'
  have hlim : Tendsto (fun k => 1 - P {ω | rootP (B k ω) (hN k) ∉ U}) atTop (𝓝 1) := by
    have := (ENNReal.Tendsto.sub tendsto_const_nhds hbad (Or.inl ENNReal.one_ne_top))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlow
    (Eventually.of_forall fun k => prob_le_one)

end QuantumNLS.LabelBlock

#print axioms QuantumNLS.LabelBlock.block_of_cuts
#print axioms QuantumNLS.LabelBlock.label_block_uniform
#print axioms QuantumNLS.LabelBlock.label_block_seq
#print axioms QuantumNLS.LabelBlock.label_block_prob
