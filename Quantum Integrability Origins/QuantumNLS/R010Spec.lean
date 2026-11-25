import QuantumNLS.TerraMultiRound80Weighted
/-! integrator-authored trusted spec for REG-010 (terra_review r228 ACCEPT): headline statement(s) copied verbatim from TerraMultiRound80Weighted (QuantumNLS.TerraMultiRound80Weighted). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.R010Spec
open QuantumNLS.TerraMultiRound80Weighted
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem REG010_spec (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    (∀ u : L2T L,
      ((∃ v : H02 L s, v.val = u) ↔
        Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ∧
      (Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
        Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
          (QuantumNLS.RootIndexedMasses.masses hκ u).1 n))) ∧
    (∀ (u : H02 L s) (n : ℤ), coordinate (L := L) s (actions κ hκ s hs0 hs2 u) n =
      (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) ∧
    (∀ a : WeightedL1 L s, ‖a‖ = ∑' n : ℤ, (1+|momentum L n|)^(2*s) * |coordinate (L := L) s a n|) ∧
    Continuous (actions κ hκ s hs0 hs2 : H02 L s → WeightedL1 L s) ∧
    ∀ B : Set (H02 L s), Bornology.IsBounded B →
      Bornology.IsBounded ((actions κ hκ s hs0 hs2) '' B) := by
  exact QuantumNLS.TerraMultiRound80Weighted.REG010 κ hκ s hs0 hs2

/-- integrator pin: the weighted carrier is literally ℓ¹(ℤ). -/
theorem weightedL1_literal (L s : ℝ) : WeightedL1 L s = lp (fun _ : ℤ => ℝ) 1 := rfl
/-- integrator pin: `coordinate` divides by the printed weight. -/
theorem coordinate_literal (s : ℝ) (a : WeightedL1 L s) (n : ℤ) :
    coordinate (L := L) s a n = a n / (1+|momentum L n|)^(2*s) := rfl
/-- integrator pin: `actions` has entries (1+|p_n|)^{2s} · I_n(u). -/
theorem actions_literal (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (u : H02 L s) (n : ℤ) :
    actions κ hκ s hs0 hs2 u n = (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n :=
  QuantumNLS.TerraMultiRound80Carrier.weightedActions_apply κ hκ s hs0 hs2 u n

end QuantumNLS.R010Spec
#print axioms QuantumNLS.R010Spec.REG010_spec
#print axioms QuantumNLS.R010Spec.actions_literal
