import QuantumNLS.Reg010LowFinal
import QuantumNLS.TerraMultiRound77L4MomentContinuity
import QuantumNLS.TerraMultiRound77FreeContinuity

/-! Same-order low fractional physical moment continuity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Sobolev
open QuantumNLS.Reg010LowEmbeddingMap QuantumNLS.Reg010LowL4Space
open QuantumNLS.TerraMultiRound77FreeContinuity QuantumNLS.TerraMultiRound77L4MomentContinuity
namespace QuantumNLS.TerraMultiRound78LowContinuity

variable {L : ℝ} [Fact (0 < L)]

theorem physical_low_power_continuous (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) :
    Continuous (fun u : H02 L s => ∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ u.val) := by
  by_cases hsmall : s < 1/2
  · exact physical_power_continuous κ hκ s hs0 hsmall
  · have hthird : (1:ℝ)/3 ≤ s := by linarith
    let i : H02 L s →L[ℂ] L4T L := embeddingH02.comp (H02.mono hthird)
    have hi (u : H02 L s) : toL2 (i u) = u.val := by
      change toL2 (embeddingH02 (H02.mono hthird u)) = u.val
      rw [embeddingH02_toL2]
      exact QuantumNLS.Reg010LowFinal.H02_lower_val (1/3) s hthird u
    rw [continuous_iff_seqContinuous]
    intro u v hu
    have h := physical_moment_tendsto_of_free_L4 hκ (fun j => i (u j)) (i v) s hs0 hs1
      (i.continuous.tendsto v |>.comp hu)
      (fun j => by rw [hi]; exact free_power_integrable s hs0.le (u j))
      (by rw [hi]; exact free_power_integrable s hs0.le v)
      (by simpa only [hi, Function.comp_def] using ((free_power_continuous (L := L) s hs0.le).tendsto v).comp hu)
    simpa only [hi, Function.comp_def] using h

#print axioms physical_low_power_continuous
end QuantumNLS.TerraMultiRound78LowContinuity
