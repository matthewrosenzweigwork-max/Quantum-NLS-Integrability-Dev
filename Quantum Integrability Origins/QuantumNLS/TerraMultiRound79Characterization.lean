import QuantumNLS.TerraMultiRound79Zero
import QuantumNLS.TerraMultiRound78Characterization

/-! The printed shifted finiteness equivalences on the entire closed interval. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound79Characterization
variable {L : ℝ} [Fact (0 < L)]

theorem closed_interval_characterization (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    ((∃ v : H02 L s, v.val = u) ↔
      Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ∧
    (Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) := by
  by_cases hs : s = 0
  · subst s
    obtain ⟨hH, hM, hI⟩ := QuantumNLS.TerraMultiRound79Zero.zero_order_characterization κ hκ u
    exact ⟨⟨fun _ => hM, fun _ => hH⟩, ⟨fun _ => hI, fun _ => hM⟩⟩
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    haveI : IsFiniteMeasure (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
      rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas]
      infer_instance
    have hshift := QuantumNLS.TerraMultiRound77ActionCriteria.shifted_power_iff
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) (2*s) (by positivity)
    have hfull := QuantumNLS.TerraMultiRound78Characterization.full_interval_characterization κ hκ u s hspos hs2
    exact ⟨hfull.1.symm.trans hshift.symm, hshift.trans hfull.2⟩

#print axioms closed_interval_characterization
end QuantumNLS.TerraMultiRound79Characterization
