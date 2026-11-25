import QuantumNLS.TerraMultiRound79Characterization
import QuantumNLS.TerraMultiRound79IndexedTail

/-! Summability and bounded-cutoff control for same-order action differences. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound79ActionDifference
variable {L : ℝ} [Fact (0 < L)]

theorem weighted_difference_summable (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (u v : H02 L s) :
    Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
      |(QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n -
       (QuantumNLS.RootIndexedMasses.masses hκ v.val).1 n|) := by
  have hu := ((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ u.val s hs0 hs2).2).mp
    (((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ u.val s hs0 hs2).1).mp ⟨u, rfl⟩)
  have hv := ((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ v.val s hs0 hs2).2).mp
    (((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ v.val s hs0 hs2).1).mp ⟨v, rfl⟩)
  apply (hu.add hv).of_nonneg_of_le
  · intro n; positivity
  · intro n
    have hu0 := (QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ u.val).2.1 n
    have hv0 := (QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ v.val).2.1 n
    have habs : |(QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n -
        (QuantumNLS.RootIndexedMasses.masses hκ v.val).1 n| ≤
        (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n +
        (QuantumNLS.RootIndexedMasses.masses hκ v.val).1 n := by
      calc
        _ ≤ |(QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n| +
            |(QuantumNLS.RootIndexedMasses.masses hκ v.val).1 n| := by
              simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
                ((QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n)
                (-(QuantumNLS.RootIndexedMasses.masses hκ v.val).1 n)
        _ = _ := by rw [abs_of_nonneg hu0, abs_of_nonneg hv0]
    have hweight : 0 ≤ (1+|momentum L n|)^(2*s) := by positivity
    have hm := mul_le_mul_of_nonneg_left habs hweight
    dsimp only [Pi.add_apply]
    nlinarith

theorem weight_bounded_on_cutoff (s R : ℝ) (hs : 0 ≤ s) (n : ℤ)
    (hn : |momentum L n| ≤ R) :
    (1+|momentum L n|)^(2*s) ≤ (1+max R 0)^(2*s) := by
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  linarith [le_max_left R 0]

#print axioms weighted_difference_summable
#print axioms weight_bounded_on_cutoff
end QuantumNLS.TerraMultiRound79ActionDifference
