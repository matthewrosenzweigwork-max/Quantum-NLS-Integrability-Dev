import QuantumNLS.LabelExactSeparation

/-!
# PROP-003 (thm:B3-exact-separation), owner decision D1 restatement

Owner decision D1 (2026-11-16): a DEF-043 regular cut is EVERY `x ∉ supp μ` with `F(x)/(2π)` not an integer; separation
holds at every such `x`, with the unique integer `a` satisfying `2πa < F(x) < 2π(a+1)`.

Restatement convention (Terra r207): replace `(S : IndexedScalarMeasureCuts L κ)` by `(S : IndexedScalarMeasure L κ)`
(the full-exterior scalar interface, whose `separation` field is assumed at every exterior `x` with the strict force
inequalities, i.e. at every D1 regular cut), replace each cut-membership hypothesis `x ∈ S.cuts` by `x ∉ S.μ.support`,
and keep every other binder, hypothesis and conclusion verbatim from `PROP003Spec` (STATUS lines 441-486).

The single headline `exact_separation_d1` is the conjunction of the four `PROP003Spec` statements
(`exact_separation_seq_spec`, `exact_separation_uniform_spec`, `no_roots_near_spec`, `lt_iff_label_le_spec`), each
as a universally quantified statement with the binder list of the accepted spec (including its dead shadowed binders).
It is proved from the accepted theorems of the frozen module `LabelExactSeparation` applied to `S.toCuts`.
No hypothesis is added; no frozen module is edited.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace QuantumNLS.D1Prop003

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelWeakJointLimit
  QuantumNLS.LabelSeparationCore QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
  QuantumNLS.EmpiricalRapidity
open QuantumNLS QuantumNLS.LabelExactSeparation

set_option maxHeartbeats 4000000 in
/-- **PROP-003, owner decision D1**: exact separation at every exterior point (sequence form, uniform form)
together with the two elementary consequences. -/
theorem exact_separation_d1 :
    (∀ {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
      {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)}
      {μ : MeasureTheory.ProbabilityMeasure ℝ} (S : IndexedScalarMeasure L κ)
      (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hμ : (μ : Measure ℝ) = S.μ)
      (hNtop : Tendsto N atTop atTop) {x : ℝ} (hx : x ∉ S.μ.support) {a : ℤ}
      (h1 : 2 * Real.pi * a < exteriorForce L κ S.μ x)
      (h2 : exteriorForce L κ S.μ x < 2 * Real.pi * (a + 1)),
      ∃ δ > 0, ∀ᶠ k in atTop, ∀ j, ((B k).n j ≤ a → (B k).q j < x - δ) ∧
        (a + 1 ≤ (B k).n j → x + δ < (B k).q j)) ∧
    (∀ {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
      {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)}
      {μ : MeasureTheory.ProbabilityMeasure ℝ} {L κ : ℝ} (S : IndexedScalarMeasure L κ)
      {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {x : ℝ} (hx : x ∉ S.μ.support) {a : ℤ}
      (h1 : 2 * Real.pi * a < exteriorForce L κ S.μ x)
      (h2 : exteriorForce L κ S.μ x < 2 * Real.pi * (a + 1)),
      ∃ δ > 0, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
        ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
          ∀ j, (B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j)) ∧
    (∀ {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
      {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)}
      {μ : MeasureTheory.ProbabilityMeasure ℝ} {L κ : ℝ} {N : ℕ} (B : OnShellBethe L κ N) {a : ℤ}
      {x δ : ℝ}
      (h : ∀ j, (B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j)) (j : Fin N),
      B.q j ∉ Icc (x - δ) (x + δ)) ∧
    (∀ {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
      {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)}
      {μ : MeasureTheory.ProbabilityMeasure ℝ} {L κ : ℝ} {N : ℕ} (B : OnShellBethe L κ N) {a : ℤ}
      {x δ : ℝ} (hδ : 0 < δ)
      (h : ∀ j, (B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j)) (j : Fin N),
      B.q j < x ↔ B.n j ≤ a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L κ N hN B μ S hconv hμ hNtop x hx a h1 h2
    exact QuantumNLS.LabelExactSeparation.exact_separation_seq S.toCuts hconv hμ hNtop hx h1 h2
  · intro _ _ _ _ _ _ L κ S μ hμ x hx a h1 h2
    exact QuantumNLS.LabelExactSeparation.exact_separation_uniform S.toCuts hμ hx h1 h2
  · intro _ _ _ _ _ _ L κ N B a x δ h j
    exact QuantumNLS.LabelExactSeparation.no_roots_near B h j
  · intro _ _ _ _ _ _ L κ N B a x δ hδ h j
    exact QuantumNLS.LabelExactSeparation.lt_iff_label_le B hδ h j

end QuantumNLS.D1Prop003

#print axioms QuantumNLS.D1Prop003.exact_separation_d1
