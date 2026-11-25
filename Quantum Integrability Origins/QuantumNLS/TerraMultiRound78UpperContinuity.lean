import QuantumNLS.TerraMultiRound78UpperEquivalence
import QuantumNLS.TerraMultiRound77FreeContinuity
import QuantumNLS.Reg010LowFinal

/-! Same-order upper fractional physical moment continuity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound77FreeContinuity QuantumNLS.TerraMultiRound78UpperEquivalence
open QuantumNLS.TerraMultiRound78UpperPhysical QuantumNLS.TerraMultiRound75Correction
namespace QuantumNLS.TerraMultiRound78UpperContinuity

variable {L : ℝ} [Fact (0 < L)]

theorem physical_upper_power_continuous (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs1 : 1 < s) (hs2 : s < 2) :
    Continuous (fun u : H02 L s => ∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ u.val) := by
  have hst : ((1:ℕ):ℝ) ≤ s := by simpa only [Nat.cast_one] using (le_of_lt hs1)
  let i : H02 L s →L[ℂ] Hk L 1 := H02.mono hst
  have hi (u : H02 L s) : (i u).val = u.val :=
    QuantumNLS.Reg010LowFinal.H02_lower_val ((1:ℕ):ℝ) s hst u
  let K : ℝ := 2 / (∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1)
  have hid (u : H02 L s) :
      (∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ u.val) =
      (∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L u.val) + K * correction κ hκ s (i u) := by
    have hf := free_power_integrable s (by linarith) u
    have hf' : Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L (i u).val) := by
      rw [hi]; exact hf
    have hm := (physical_free_upper_iff κ hκ (i u) s hs1 hs2).mpr hf'
    have hh := physical_free_upper_finite κ hκ (i u) s hs1 hs2 hm hf'
    rw [hi] at hh
    have hh' := sub_eq_iff_eq_add.mp hh
    simpa only [add_comm] using hh' 
  rw [continuous_iff_seqContinuous]
  intro u v hu
  have hfree := ((free_power_continuous (L := L) s (by linarith)).tendsto v).comp hu
  have hcor := ((correction_continuous κ hκ s hs1 hs2).tendsto (i v)).comp
    (i.continuous.tendsto v |>.comp hu)
  have h := hfree.add (hcor.const_mul K)
  rw [← hid v] at h
  exact h.congr' (Eventually.of_forall fun j => (hid (u j)).symm)

#print axioms physical_upper_power_continuous
end QuantumNLS.TerraMultiRound78UpperContinuity
