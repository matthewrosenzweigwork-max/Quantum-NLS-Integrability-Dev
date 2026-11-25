import QuantumNLS.Ext025BMeasure

/-! EXT-025 layer A (part 2), haiku_inventory. Contract GP-12 =
FIN-EXT025-GP-12 (Fatou and lower semicontinuity of positive form energy),
stated at the literal text of FINAL_EXTERNAL_THEOREM_INSTANCES.json:
  hypotheses: scalar functions nonnegative and measurable on a fixed measure
  space; for operator forms, finite-rank or bounded spectral truncations give
  nonnegative bounded tests;
  conclusion: the integral of the lower limit does not exceed the lower limit of
  the integrals; suprema of bounded positive truncations give the corresponding
  form-energy lower semicontinuity.
Modelling note: the record does not name the topology on the states. The second
clause is stated on an arbitrary topological space X with tests q n : X → [0,∞]
that are bounded and continuous (continuity of the bounded tests in the relevant
topology, e.g. trace norm, is the consumer obligation, as the record says). -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal

namespace QuantumNLS.Ext025HGP12

/-- Exact contract GP-12. -/
theorem contract_GP12 :
    (∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ≥0∞),
      (∀ n, Measurable (f n)) →
      (∫⁻ x, liminf (fun n => f n x) atTop ∂μ) ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop) ∧
    (∀ {X : Type*} [TopologicalSpace X] (q : ℕ → X → ℝ≥0∞),
      (∀ n, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x, q n x ≤ C) →
      (∀ n, Continuous (q n)) →
      LowerSemicontinuous (fun x => ⨆ n, q n x)) := by
  refine ⟨fun {α} _ μ f hf => ?_, fun {X} _ q _ hq => ?_⟩
  · exact QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-12» (μ := μ) f hf
  · exact lowerSemicontinuous_iSup (fun n => (hq n).lowerSemicontinuous)

end QuantumNLS.Ext025HGP12

#print axioms QuantumNLS.Ext025HGP12.contract_GP12
