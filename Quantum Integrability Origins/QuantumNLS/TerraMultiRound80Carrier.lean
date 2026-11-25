import QuantumNLS.TerraMultiRound80Continuity

/-! The weighted action map as a concrete ℓ¹-valued map. -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound80Carrier
variable {L : ℝ} [Fact (0 < L)]

def weightedActions (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2)
    (u : H02 L s) : lp (fun _ : ℤ => ℝ) 1 :=
  ⟨fun n => (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n, by
    apply memℓp_gen
    have h := ((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ u.val s hs0 hs2).2).mp
      (((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ u.val s hs0 hs2).1).mp ⟨u, rfl⟩)
    have hn : ∀ n : ℤ, |(1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n| =
        (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n := by
      intro n
      exact abs_of_nonneg (mul_nonneg (by positivity) ((QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ u.val).2.1 n))
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs, hn] using h⟩

theorem weightedActions_apply (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2)
    (u : H02 L s) (n : ℤ) : weightedActions κ hκ s hs0 hs2 u n =
      (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n := rfl

theorem weightedActions_continuous (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    Continuous (weightedActions κ hκ s hs0 hs2 : H02 L s → lp (fun _ : ℤ => ℝ) 1) := by
  by_cases hz : s = 0
  · subst s
    have heq : weightedActions κ hκ 0 (by norm_num) (by norm_num) =
        (fun u : H02 L 0 => (QuantumNLS.RootIndexedMasses.masses hκ u.val).1) := by
      funext u
      apply Subtype.ext
      funext n
      simp [weightedActions_apply]
    rw [heq]
    exact QuantumNLS.TerraMultiRound79Zero.zero_actions_continuous κ hκ
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hz)
    rw [continuous_iff_seqContinuous]
    intro u v hu
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hd := QuantumNLS.TerraMultiRound80Continuity.weighted_action_difference_tendsto κ hκ s hspos hs2 u v hu
    have he : ∀ j, ‖weightedActions κ hκ s hs0 hs2 (u j) - weightedActions κ hκ s hs0 hs2 v‖ =
        ∑' n : ℤ, (1+|momentum L n|)^(2*s) *
          |(QuantumNLS.RootIndexedMasses.masses hκ (u j).val).1 n -
           (QuantumNLS.RootIndexedMasses.masses hκ v.val).1 n| := by
      intro j
      have h := lp.norm_rpow_eq_tsum (p := (1 : ℝ≥0∞)) (by norm_num)
        (weightedActions κ hκ s hs0 hs2 (u j) - weightedActions κ hκ s hs0 hs2 v)
      simp only [ENNReal.toReal_one, Real.rpow_one, lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs,
        weightedActions_apply] at h
      rw [h]
      apply tsum_congr
      intro n
      rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ (1+|momentum L n|)^(2*s) by positivity)]
    exact hd.congr' (Filter.Eventually.of_forall fun j => (he j).symm)

#print axioms weightedActions_apply
#print axioms weightedActions_continuous
end QuantumNLS.TerraMultiRound80Carrier
