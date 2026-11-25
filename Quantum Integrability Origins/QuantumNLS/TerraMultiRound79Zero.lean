import QuantumNLS.TerraMultiRound68Endpoints
import QuantumNLS.SobolevSpaces

/-! The complete zero-order characterization and action mapping. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev
open QuantumNLS.TerraMultiRound68Endpoints
namespace QuantumNLS.TerraMultiRound79Zero
variable {L : ℝ} [Fact (0 < L)]

theorem zero_order_characterization (κ : ℝ) (hκ : 0 < κ) (u : L2T L) :
    (∃ v : H02 L 0, v.val = u) ∧
    Integrable (fun t : ℝ => (1+|t|) ^ (2*(0:ℝ))) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ∧
    Summable (fun n : ℤ => (1+|QuantumNLS.RootWeightedCellsR26.momentum L n|)^(2*(0:ℝ)) *
      (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
  haveI : IsFiniteMeasure (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
    rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas]
    infer_instance
  refine ⟨H02.exists_zero u, ?_, ?_⟩
  · simpa using (integrable_const (1:ℝ) : Integrable (fun _ : ℝ => (1:ℝ))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ u))
  · simpa using (endpoint_results L κ hκ).1 u |>.2.1

theorem zero_actions_continuous (κ : ℝ) (hκ : 0 < κ) :
    Continuous (fun u : H02 L 0 => (QuantumNLS.RootIndexedMasses.masses hκ u.val).1) := by
  exact continuous_subtype_val.comp ((QuantumNLS.DEF014Continuity.continuous_physical_masses hκ).comp
    (H02.toL2 (L := L) (s := 0) (by norm_num)).continuous)

theorem zero_actions_bounded (κ : ℝ) (hκ : 0 < κ) (B : Set (H02 L 0))
    (hB : Bornology.IsBounded B) :
    Bornology.IsBounded ((fun u : H02 L 0 => (QuantumNLS.RootIndexedMasses.masses hκ u.val).1) '' B) := by
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp hB
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨K^2, ?_⟩
  rintro a ⟨u, hu, rfl⟩
  rw [(endpoint_results L κ hκ).1 u.val |>.2.2.2, H02.norm_zero]
  exact pow_le_pow_left₀ (norm_nonneg _) (hK u hu) 2

#print axioms zero_order_characterization
#print axioms zero_actions_continuous
#print axioms zero_actions_bounded
end QuantumNLS.TerraMultiRound79Zero
