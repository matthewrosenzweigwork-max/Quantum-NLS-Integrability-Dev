import QuantumNLS.TerraMultiRound80Final

/-! The weighted ℓ¹ carrier, represented isometrically by weighted coordinates.
`coordinate` recovers the actual unweighted action values. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound80Weighted
variable {L : ℝ} [Fact (0 < L)]

abbrev WeightedL1 (_L _s : ℝ) := lp (fun _ : ℤ => ℝ) 1

def coordinate (s : ℝ) (a : WeightedL1 L s) (n : ℤ) : ℝ :=
  a n / (1+|momentum L n|)^(2*s)

def actions (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2)
    (u : H02 L s) : WeightedL1 L s :=
  QuantumNLS.TerraMultiRound80Carrier.weightedActions κ hκ s hs0 hs2 u

theorem coordinate_actions (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2)
    (u : H02 L s) (n : ℤ) : coordinate (L := L) s (actions κ hκ s hs0 hs2 u) n =
      (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n := by
  have hw : (1+|momentum L n|)^(2*s) ≠ 0 := ne_of_gt (by positivity)
  simp only [coordinate, actions, QuantumNLS.TerraMultiRound80Carrier.weightedActions_apply]
  exact mul_div_cancel_left₀ _ hw

theorem norm_eq_weighted_coordinates (s : ℝ) (a : WeightedL1 L s) :
    ‖a‖ = ∑' n : ℤ, (1+|momentum L n|)^(2*s) * |coordinate (L := L) s a n| := by
  have h := lp.norm_rpow_eq_tsum (p := (1 : ℝ≥0∞)) (by norm_num) a
  simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] at h
  rw [h]
  apply tsum_congr
  intro n
  have hw : 0 < (1+|momentum L n|)^(2*s) := by positivity
  simp only [coordinate, abs_div, abs_of_pos hw]
  field_simp

/-- The entire printed REG-010 theorem on the actual action coordinates,
with the weighted ℓ¹ norm built into `WeightedL1`. -/
theorem REG010 (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
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
  refine ⟨fun u => QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ u s hs0 hs2,
    coordinate_actions κ hκ s hs0 hs2, norm_eq_weighted_coordinates (L := L) s, ?_, ?_⟩
  · exact QuantumNLS.TerraMultiRound80Carrier.weightedActions_continuous κ hκ s hs0 hs2
  · exact QuantumNLS.TerraMultiRound80Final.weighted_actions_bounded κ hκ s hs0 hs2

#print axioms coordinate_actions
#print axioms norm_eq_weighted_coordinates
#print axioms REG010
end QuantumNLS.TerraMultiRound80Weighted
