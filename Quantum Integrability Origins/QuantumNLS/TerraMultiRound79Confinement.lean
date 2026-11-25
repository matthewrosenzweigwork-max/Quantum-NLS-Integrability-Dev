import QuantumNLS.TerraMultiRound79MomentTails
import QuantumNLS.TerraMultiRound71Tail

/-! Uniform confinement for convergent Sobolev sequences. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound79Confinement
variable {L : ℝ} [Fact (0 < L)]

theorem common_displacement_bound (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs : 0 ≤ s)
    (u : ℕ → H02 L s) (v : H02 L s) (hu : Tendsto u atTop (𝓝 v)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j, 2 * Real.sqrt (κ * ‖(u j).val‖^2 / L) ≤ B := by
  have ht : Tendsto (fun j => (u j).val) atTop (𝓝 v.val) :=
    ((H02.toL2 (L := L) hs).continuous.tendsto v).comp hu
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ ht)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK _ ⟨0, rfl⟩)
  refine ⟨2 * Real.sqrt (κ * K^2 / L), by positivity, ?_⟩
  intro j
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (le_of_lt (Fact.out : 0 < L))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hK _ ⟨j, rfl⟩) 2) hκ.le

theorem indexed_tails_under_common_confinement (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs : 0 ≤ s) (u : ℕ → H02 L s) (v : H02 L s) (hu : Tendsto u atTop (𝓝 v)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j (R : ℝ),
      (∑' n : ℤ, if R+B < |momentum L n| then ENNReal.ofReal
        ((1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ (u j).val).1 n) else 0) ≤
      ENNReal.ofReal ((1+B)^(2*s)) *
        ∫⁻ t : ℝ, if R < |t| then ENNReal.ofReal ((1+|t|)^(2*s)) else 0
          ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j).val := by
  obtain ⟨B, hB, hb⟩ := common_displacement_bound κ hκ s hs u v hu
  exact ⟨B, hB, fun j R => QuantumNLS.TerraMultiRound71Tail.indexed_tail_le_common_bound
    hκ (u j).val (2*s) R B (by positivity) (hb j)⟩

#print axioms common_displacement_bound
#print axioms indexed_tails_under_common_confinement
end QuantumNLS.TerraMultiRound79Confinement
