import QuantumNLS.TerraMultiRound79Confinement
import QuantumNLS.TerraMultiRound79ShiftedTail

/-! Same-order uniform shifted tails of the physical indexed actions. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound79IndexedTail
variable {L : ℝ} [Fact (0 < L)]

theorem uniform_indexed_action_tail (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 < s) (hs2 : s ≤ 2) (u : ℕ → H02 L s) (v : H02 L s)
    (hu : Tendsto u atTop (𝓝 v)) :
    ∀ ε > 0, ∃ R : ℝ, ∀ j,
      (∑' n : ℤ, if R < |momentum L n| then ENNReal.ofReal
        ((1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ (u j).val).1 n) else 0) <
        ENNReal.ofReal ε := by
  obtain ⟨B, hB, hb⟩ := QuantumNLS.TerraMultiRound79Confinement.indexed_tails_under_common_confinement
    κ hκ s hs0.le u v hu
  let C : ℝ := (1+B)^(2*s)
  have hC : 0 < C := by dsimp [C]; positivity
  intro ε hε
  obtain ⟨R, hR, ht⟩ := QuantumNLS.TerraMultiRound79ShiftedTail.uniform_shifted_physical_tail
    κ hκ s hs0 hs2 u v hu (ε/(C+1)) (by positivity)
  refine ⟨R+B, ?_⟩
  intro j
  have hprod : ENNReal.ofReal C * ENNReal.ofReal (ε/(C+1)) < ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul hC.le]
    apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < C+1)).mpr
    nlinarith
  have hh := mul_le_mul' (le_rfl : ENNReal.ofReal C ≤ ENNReal.ofReal C) (le_of_lt (ht j))
  exact lt_of_le_of_lt ((hb j R).trans hh) hprod

#print axioms uniform_indexed_action_tail
end QuantumNLS.TerraMultiRound79IndexedTail
