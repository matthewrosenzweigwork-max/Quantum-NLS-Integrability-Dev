import QuantumNLS.TerraMultiRound79Endpoints
import QuantumNLS.TerraMultiRound78LowContinuity
import QuantumNLS.TerraMultiRound78UpperContinuity
import QuantumNLS.TerraMultiRound78Characterization
import QuantumNLS.TerraMultiRound75PhysicalUniformTail

/-! Same-order moment continuity and uniform physical tails throughout (0,2]. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev
namespace QuantumNLS.TerraMultiRound79MomentTails
variable {L : ℝ} [Fact (0 < L)]

theorem physical_moment_continuous (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 < s) (hs2 : s ≤ 2) :
    Continuous (fun u : H02 L s => ∫ x : ℝ, |x| ^ (2*s) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) := by
  by_cases hlow : s < 1
  · exact QuantumNLS.TerraMultiRound78LowContinuity.physical_low_power_continuous κ hκ s hs0 hlow
  · by_cases hone : s = 1
    · subst s
      exact QuantumNLS.TerraMultiRound79Endpoints.physical_one_continuous κ hκ
    · by_cases htwo : s = 2
      · subst s
        exact QuantumNLS.TerraMultiRound79Endpoints.physical_two_continuous κ hκ
      · exact QuantumNLS.TerraMultiRound78UpperContinuity.physical_upper_power_continuous κ hκ s
          (lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm hone)) (lt_of_le_of_ne hs2 htwo)

theorem physical_uniform_tail_on_Hs (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 < s) (hs2 : s ≤ 2) (u : ℕ → H02 L s) (v : H02 L s)
    (hu : Tendsto u atTop (𝓝 v)) :
    ∀ ε > 0, ∃ k : ℕ, ∀ j,
      (∫ t : ℝ, if 2 * (k : ℝ) < |t| ^ (2*s) then |t| ^ (2*s) else 0
        ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j).val) < ε := by
  apply QuantumNLS.TerraMultiRound75PhysicalUniformTail.physical_uniform_power_tail hκ
    (fun j => (u j).val) v.val (2*s) (by positivity)
  · exact ((H02.toL2 (L := L) hs0.le).continuous.tendsto v).comp hu
  · intro j
    exact (QuantumNLS.TerraMultiRound78Characterization.full_interval_characterization κ hκ (u j).val s hs0 hs2).1.mpr ⟨u j, rfl⟩
  · exact (QuantumNLS.TerraMultiRound78Characterization.full_interval_characterization κ hκ v.val s hs0 hs2).1.mpr ⟨v, rfl⟩
  · exact ((physical_moment_continuous κ hκ s hs0 hs2).tendsto v).comp hu

#print axioms physical_moment_continuous
#print axioms physical_uniform_tail_on_Hs
end QuantumNLS.TerraMultiRound79MomentTails
