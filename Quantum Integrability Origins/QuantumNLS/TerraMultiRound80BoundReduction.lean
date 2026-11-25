import QuantumNLS.TerraMultiRound80BoundBridge

/-! Reduction of bounded action mapping to a physical moment bound. -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound80BoundReduction
variable {L : ℝ} [Fact (0 < L)]

/-- A uniform bound on the actual physical shifted moment over a bounded
Sobolev set yields boundedness of the actual weighted action map. The moment
bound is an explicit intermediate premise, not the REG-010 conclusion. -/
theorem bounded_actions_of_physical_bound (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (B : Set (H02 L s)) (hB : Bornology.IsBounded B)
    (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ u ∈ B, (∫⁻ t : ℝ, ENNReal.ofReal ((1+|t|)^(2*s))
      ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) ≤ ENNReal.ofReal M) :
    Bornology.IsBounded ((QuantumNLS.TerraMultiRound80Carrier.weightedActions κ hκ s hs0 hs2) '' B) := by
  obtain ⟨C, hC, hc⟩ := QuantumNLS.TerraMultiRound80BoundBridge.bounded_set_action_physical_bridge κ hκ s hs0 B hB
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C*M, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  let f : ℤ → ℝ := fun n => (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    exact mul_nonneg (by positivity) ((QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ u.val).2.1 n)
  have hfs : Summable f := ((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ u.val s hs0 hs2).2).mp
      (((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ u.val s hs0 hs2).1).mp ⟨u, rfl⟩)
  have hn : ‖QuantumNLS.TerraMultiRound80Carrier.weightedActions κ hκ s hs0 hs2 u‖ = ∑' n, f n := by
    have h := lp.norm_rpow_eq_tsum (p := (1 : ℝ≥0∞)) (by norm_num)
      (QuantumNLS.TerraMultiRound80Carrier.weightedActions κ hκ s hs0 hs2 u)
    simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs,
      QuantumNLS.TerraMultiRound80Carrier.weightedActions_apply] at h
    rw [h]
    apply tsum_congr
    intro n
    exact abs_of_nonneg (hf n)
  have he : ENNReal.ofReal (‖QuantumNLS.TerraMultiRound80Carrier.weightedActions κ hκ s hs0 hs2 u‖) ≤ ENNReal.ofReal (C*M) := by
    rw [hn, ENNReal.ofReal_tsum_of_nonneg hf hfs, ENNReal.ofReal_mul hC]
    exact (hc u hu).trans (mul_le_mul' le_rfl (hm u hu))
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC hM)).mp he

#print axioms bounded_actions_of_physical_bound
end QuantumNLS.TerraMultiRound80BoundReduction
