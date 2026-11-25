import QuantumNLS.TerraMultiRound80Carrier

/-! The proved finiteness and continuity clauses of REG-010.
The positive-order bounded-set clause is not asserted here. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound80PartialAssembly
variable {L : ℝ} [Fact (0 < L)]

theorem reg010_finiteness_and_continuity (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    (∀ u : L2T L,
      ((∃ v : H02 L s, v.val = u) ↔
        Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ∧
      (Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
        Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
          (QuantumNLS.RootIndexedMasses.masses hκ u).1 n))) ∧
    Continuous (QuantumNLS.TerraMultiRound80Carrier.weightedActions κ hκ s hs0 hs2 : H02 L s → lp (fun _ : ℤ => ℝ) 1) := by
  exact ⟨fun u => QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ u s hs0 hs2,
    QuantumNLS.TerraMultiRound80Carrier.weightedActions_continuous κ hκ s hs0 hs2⟩

#print axioms reg010_finiteness_and_continuity
end QuantumNLS.TerraMultiRound80PartialAssembly
