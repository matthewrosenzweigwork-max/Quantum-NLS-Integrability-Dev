import QuantumNLS.TerraMultiRound80Carrier

/-! Confinement transfers bounded physical moments to bounded action moments. -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound80BoundBridge
variable {L : ℝ} [Fact (0 < L)]

/-- On a bounded Sobolev set the confinement constant can be chosen once,
so the complete shifted action moment is bounded by a common multiple of
the complete shifted physical moment. -/
theorem bounded_set_action_physical_bridge (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 ≤ s) (B : Set (H02 L s)) (hB : Bornology.IsBounded B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ B,
      (∑' n : ℤ, ENNReal.ofReal ((1+|momentum L n|)^(2*s) *
        (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n)) ≤
      ENNReal.ofReal C * ∫⁻ t : ℝ, ENNReal.ofReal ((1+|t|)^(2*s))
        ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val := by
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp hB
  let D : ℝ := 2 * Real.sqrt (κ * (max K 0)^2 / L)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨(1+D)^(2*s), by positivity, ?_⟩
  intro u hu
  have huv : ‖u.val‖ ≤ max K 0 := by
    exact (WField.norm_val_le (fun n => one_le_def002 L hs0 n) u).trans ((hK u hu).trans (le_max_left _ _))
  have hbound : 2 * Real.sqrt (κ * ‖u.val‖^2 / L) ≤ D := by
    dsimp [D]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ (Fact.out : 0 < L).le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) huv 2) hκ.le
  have h := QuantumNLS.TerraMultiRound71Tail.indexed_tail_le_common_bound hκ u.val (2*s) (-D-1) D (by positivity) hbound
  have hneg : ∀ n : ℤ, -D-1+D < |momentum L n| := by
    intro n; linarith [abs_nonneg (momentum L n)]
  have ht : ∀ t : ℝ, -D-1 < |t| := by
    intro t; linarith [abs_nonneg t]
  simpa only [hneg, ht, if_true] using h

#print axioms bounded_set_action_physical_bridge
end QuantumNLS.TerraMultiRound80BoundBridge
