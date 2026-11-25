import QuantumNLS.TerraMultiRound77FreeContinuity
import QuantumNLS.TerraMultiRound64FirstIdentity
import QuantumNLS.TerraMultiRound64FieldIdentity
import QuantumNLS.Reg010LowFinal

/-! Same-order physical moment continuity at the positive integer endpoints. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.Sobolev QuantumNLS.FreeLimit QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound77FreeContinuity QuantumNLS.TerraMultiRound62FreeMoments
open QuantumNLS.TerraMultiRound64FirstIdentity QuantumNLS.TerraMultiRound64FieldIdentity
open QuantumNLS.TerraMultiRound59RCompatibility
namespace QuantumNLS.TerraMultiRound79Endpoints

variable {L : ℝ} [Fact (0 < L)]

theorem physical_one_continuous (κ : ℝ) (hκ : 0 < κ) :
    Continuous (fun u : H02 L 1 => ∫ x : ℝ, |x| ^ (2*(1:ℝ)) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) := by
  let i : H02 L 1 →L[ℂ] Hk L 1 := H02.mono (by norm_num)
  have hi (u : H02 L 1) : (i u).val = u.val :=
    QuantumNLS.Reg010LowFinal.H02_lower_val ((1:ℕ):ℝ) 1 (by norm_num) u
  have heq (u : H02 L 1) :
      (∫ x : ℝ, |x| ^ (2*(1:ℝ)) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) =
      (∫ x : ℝ, |x| ^ (2*(1:ℝ)) ∂freeMeasure L u.val) + R1field (L := L) κ (i u) := by
    have hf := free_power_integrable (L := L) 1 (by norm_num) u
    have hf' : Integrable (fun x : ℝ => x ^ (2*1)) (freeMeasure L u.val) := by
      simpa only [mul_one, Real.rpow_two, sq_abs] using hf
    have hid := first_field_identity κ hκ (i u)
    rw [hi] at hid
    have hfree := free_finite_moment u.val 1 hf'
    simpa only [mul_one, Real.rpow_two, sq_abs] using hid.trans (congrArg (fun x => x + R1field (L := L) κ (i u)) hfree.symm)
  simp_rw [heq]
  exact (free_power_continuous (L := L) 1 (by norm_num)).add ((R1field_continuous κ).comp i.continuous)

theorem physical_two_continuous (κ : ℝ) (hκ : 0 < κ) :
    Continuous (fun u : H02 L 2 => ∫ x : ℝ, |x| ^ (2*(2:ℝ)) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) := by
  let i : H02 L 2 →L[ℂ] Hk L 1 := H02.mono (by norm_num)
  have hi (u : H02 L 2) : (i u).val = u.val :=
    QuantumNLS.Reg010LowFinal.H02_lower_val ((1:ℕ):ℝ) 2 (by norm_num) u
  have habs (x : ℝ) : |x| ^ 4 = x ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (show 0 ≤ x ^ 4 by positivity)]
  have hpow : (fun x : ℝ => |x| ^ (2*(2:ℝ))) = (fun x : ℝ => x^(2*2:ℕ)) := by
    funext x
    norm_num only
    change |x| ^ ((4:ℕ):ℝ) = x ^ 4
    rw [Real.rpow_natCast]
    exact habs x
  have heq (u : H02 L 2) :
      (∫ x : ℝ, |x| ^ (2*(2:ℝ)) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) =
      (∫ x : ℝ, |x| ^ (2*(2:ℝ)) ∂freeMeasure L u.val) + Rfield (L := L) 2 (by omega) κ (i u) := by
    have hf := free_power_integrable (L := L) 2 (by norm_num) u
    have hf' : Integrable (fun x : ℝ => x ^ (2*2)) (freeMeasure L u.val) := by
      rwa [hpow] at hf
    have hsq := representative_hsq 2 u
    have hsq' : QuantumNLS.RiccatiSobolevE1.hsq L (2:ℕ) (fun n => QuantumNLS.Fourier.coeff L (i u).val n) ≠ ⊤ := by rw [hi]; exact hsq
    have h := finite_field_identity κ hκ 2 (by omega) (i u) hsq'
    rw [hi] at h
    have hfree := free_finite_moment u.val 2 hf'
    have he := h.trans (congrArg (fun x => x + Rfield (L := L) 2 (by omega) κ (i u)) hfree.symm)
    rw [hpow]
    exact he
  simp_rw [heq]
  exact (free_power_continuous (L := L) 2 (by norm_num)).add ((Rfield_continuous 2 (by omega) κ).comp i.continuous)

#print axioms physical_one_continuous
#print axioms physical_two_continuous
end QuantumNLS.TerraMultiRound79Endpoints
