import QuantumNLS.TerraMultiRound78UpperIdentity
import QuantumNLS.TerraMultiRound75Correction

/-! Upper-order physical correction identity for finite moments. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound78UpperIdentity QuantumNLS.TerraMultiRound60Kernel
open QuantumNLS.TerraMultiRound64FieldIdentity QuantumNLS.TerraMultiRound64FreeSobolev
open QuantumNLS.Reg014Moments QuantumNLS.TerraMultiRound77YCorrection
namespace QuantumNLS.TerraMultiRound78UpperPhysical

variable {L : ℝ} [Fact (0 < L)]

theorem physical_free_upper_finite (κ : ℝ) (hκ : 0 < κ) (u : Hk L 1)
    (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2)
    (hμ : Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u.val))
    (hν : Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L u.val)) :
    (∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ u.val) -
      (∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L u.val) =
      (2 / (∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1)) *
        QuantumNLS.TerraMultiRound75Correction.correction κ hκ s u := by
  haveI : IsFiniteMeasure (freeMeasure L u.val) := by
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    infer_instance
  have hν2 : Integrable (fun t : ℝ => t ^ (2*1)) (freeMeasure L u.val) :=
    (free_even_integrable_iff_hsq u.val 1).mpr (representative_hsq 1 u)
  have h := upper_finite_correction (PhysicalQuantumMeasure.measure hκ u.val)
    (freeMeasure L u.val) s hs1 hs2 hμ hν
  have heq : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      t ^ (s-3) * ((∫ x : ℝ, kernel 2 (Real.sqrt t) x ∂PhysicalQuantumMeasure.measure hκ u.val) -
        (∫ x : ℝ, kernel 2 (Real.sqrt t) x ∂freeMeasure L u.val)) =
      t ^ (s-3) * Dfun κ hκ 2 u.val (Real.sqrt t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [free_kernel_sum (Real.sqrt_pos.2 ht) u.val 1 hν2]
    rfl
  rw [integral_congr_ae heq] at h
  have hchange := correction_change_variable (s-1) (Dfun κ hκ 2 u.val)
  have hchange' : (∫ t in Ioi 0, t ^ (s-3) * Dfun κ hκ 2 u.val (Real.sqrt t)) =
      2 * QuantumNLS.TerraMultiRound75Correction.correction κ hκ s u := by
    simpa only [show s-1-2 = s-3 by ring, show 2*(s-1)-3 = 2*s-5 by ring,
      QuantumNLS.TerraMultiRound75Correction.correction] using hchange
  rw [hchange'] at h
  have hp : s-1 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have hC := Real.integral_rpowIntegrand₀₁_one_pos hp
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (ne_of_gt hC)).2
  nlinarith

#print axioms physical_free_upper_finite
end QuantumNLS.TerraMultiRound78UpperPhysical
