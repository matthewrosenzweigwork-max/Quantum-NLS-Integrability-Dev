import QuantumNLS.TerraMultiRound80PhysicalBound
import QuantumNLS.TerraMultiRound80PartialAssembly

/-! The finiteness, weighted continuity and bounded-set clauses of REG-010. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound80Final
variable {L : ℝ} [Fact (0 < L)]

theorem weighted_actions_bounded (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2)
    (B : Set (H02 L s)) (hB : Bornology.IsBounded B) :
    Bornology.IsBounded ((QuantumNLS.TerraMultiRound80Carrier.weightedActions κ hκ s hs0 hs2) '' B) := by
  by_cases hzero : s = 0
  · subst s
    have heq : QuantumNLS.TerraMultiRound80Carrier.weightedActions κ hκ 0 (by norm_num) (by norm_num) =
        (fun u : H02 L 0 => (QuantumNLS.RootIndexedMasses.masses hκ u.val).1) := by
      funext u
      apply Subtype.ext
      funext n
      simp [QuantumNLS.TerraMultiRound80Carrier.weightedActions_apply]
    rw [heq]
    exact QuantumNLS.TerraMultiRound79Zero.zero_actions_bounded κ hκ B hB
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hzero)
    obtain ⟨M, hM, hm⟩ := QuantumNLS.TerraMultiRound80PhysicalBound.shifted_physical_bounded κ hκ s hspos hs2 B hB
    exact QuantumNLS.TerraMultiRound80BoundReduction.bounded_actions_of_physical_bound κ hκ s hs0 hs2 B hB M hM hm

/-- REG-010: the three printed finiteness conditions are equivalent, and the
actual actions define a continuous, bounded-set preserving map into weighted
ℓ¹, represented isometrically by their weighted coordinates in ordinary ℓ¹. -/
theorem REG010 (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    (∀ u : L2T L,
      ((∃ v : H02 L s, v.val = u) ↔
        Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ∧
      (Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
        Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
          (QuantumNLS.RootIndexedMasses.masses hκ u).1 n))) ∧
    (∀ (u : H02 L s) (n : ℤ), QuantumNLS.TerraMultiRound80Carrier.weightedActions κ hκ s hs0 hs2 u n =
      (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) ∧
    Continuous (QuantumNLS.TerraMultiRound80Carrier.weightedActions κ hκ s hs0 hs2 : H02 L s → lp (fun _ : ℤ => ℝ) 1) ∧
    ∀ B : Set (H02 L s), Bornology.IsBounded B →
      Bornology.IsBounded ((QuantumNLS.TerraMultiRound80Carrier.weightedActions κ hκ s hs0 hs2) '' B) := by
  refine ⟨fun u => QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ u s hs0 hs2, ?_, ?_, ?_⟩
  · exact QuantumNLS.TerraMultiRound80Carrier.weightedActions_apply κ hκ s hs0 hs2
  · exact QuantumNLS.TerraMultiRound80Carrier.weightedActions_continuous κ hκ s hs0 hs2
  · exact weighted_actions_bounded κ hκ s hs0 hs2

#print axioms weighted_actions_bounded
#print axioms REG010
end QuantumNLS.TerraMultiRound80Final
