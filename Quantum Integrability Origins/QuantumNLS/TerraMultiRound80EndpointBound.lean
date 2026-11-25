import QuantumNLS.TerraMultiRound80FreeBound
import QuantumNLS.TerraMultiRound79Endpoints
import QuantumNLS.Reg014Moments

/-! Uniform physical power moment bounds at orders one and two. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.FreeLimit QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound77FreeContinuity QuantumNLS.TerraMultiRound80FreeBound
open QuantumNLS.TerraMultiRound62FreeMoments QuantumNLS.TerraMultiRound64FirstIdentity
open QuantumNLS.TerraMultiRound64FieldIdentity QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.TerraMultiRound59PolynomialProperty QuantumNLS.Reg014Moments
namespace QuantumNLS.TerraMultiRound80EndpointBound
variable {L : ℝ} [Fact (0 < L)]

theorem physical_one_bounded (κ : ℝ) (hκ : 0 < κ) (B : Set (H02 L 1)) (hB : Bornology.IsBounded B) :
    ∃ M : ℝ, ∀ u ∈ B, (∫ x : ℝ, |x|^(2*(1:ℝ)) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) ≤ M := by
  let i : H02 L 1 →L[ℂ] Hk L 1 := H02.mono (by norm_num)
  have hi (u : H02 L 1) : (i u).val = u.val :=
    QuantumNLS.Reg010LowFinal.H02_lower_val ((1:ℕ):ℝ) 1 (by norm_num) u
  have hA : Bornology.IsBounded (i '' B) := i.lipschitz.isBounded_image hB
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp hB
  obtain ⟨U, hU⟩ := isBounded_iff_forall_norm_le.mp hA
  obtain ⟨R, hR⟩ := RealPolynomial_bounded (R1field_polynomial (L := L) κ) U
  refine ⟨(max K 0)^2 + R, ?_⟩
  intro u hu
  have hf := free_power_le_sobolev_norm (L := L) 1 (by norm_num) u
  have hK2 : ‖u‖^2 ≤ (max K 0)^2 := pow_le_pow_left₀ (norm_nonneg _) ((hK u hu).trans (le_max_left _ _)) 2
  have hr := hR (i u) (hU (i u) ⟨u, hu, rfl⟩)
  have heq : (∫ x : ℝ, |x|^(2*(1:ℝ)) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) =
      (∫ x : ℝ, |x|^(2*(1:ℝ)) ∂freeMeasure L u.val) + R1field (L := L) κ (i u) := by
    have hfi := free_power_integrable (L := L) 1 (by norm_num) u
    have hfi' : Integrable (fun x : ℝ => x ^ (2*1)) (freeMeasure L u.val) := by
      simpa only [mul_one, Real.rpow_two, sq_abs] using hfi
    have hid := first_field_identity κ hκ (i u)
    rw [hi] at hid
    have hfree := free_finite_moment u.val 1 hfi'
    simpa only [mul_one, Real.rpow_two, sq_abs] using hid.trans (congrArg (fun x => x + R1field (L := L) κ (i u)) hfree.symm)
  linarith [le_abs_self (R1field (L := L) κ (i u))]

theorem physical_two_bounded (κ : ℝ) (hκ : 0 < κ) (B : Set (H02 L 2)) (hB : Bornology.IsBounded B) :
    ∃ M : ℝ, ∀ u ∈ B, (∫ x : ℝ, |x|^(2*(2:ℝ)) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) ≤ M := by
  let i : H02 L 2 →L[ℂ] Hk L 1 := H02.mono (by norm_num)
  have hi (u : H02 L 2) : (i u).val = u.val :=
    QuantumNLS.Reg010LowFinal.H02_lower_val ((1:ℕ):ℝ) 2 (by norm_num) u
  have hA : Bornology.IsBounded (i '' B) := i.lipschitz.isBounded_image hB
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp hB
  obtain ⟨U, hU⟩ := isBounded_iff_forall_norm_le.mp hA
  obtain ⟨R, hR⟩ := RealPolynomial_bounded (Rfield_polynomial (L := L) 2 (by omega) κ) U
  refine ⟨(max K 0)^2 + R, ?_⟩
  intro u hu
  have hf := free_power_le_sobolev_norm (L := L) 2 (by norm_num) u
  have hK2 : ‖u‖^2 ≤ (max K 0)^2 := pow_le_pow_left₀ (norm_nonneg _) ((hK u hu).trans (le_max_left _ _)) 2
  have hr := hR (i u) (hU (i u) ⟨u, hu, rfl⟩)
  have habs (x : ℝ) : |x| ^ 4 = x ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (show 0 ≤ x ^ 4 by positivity)]
  have hpow : (fun x : ℝ => |x| ^ (2*(2:ℝ))) = (fun x : ℝ => x^(2*2:ℕ)) := by
    funext x
    norm_num only
    change |x| ^ ((4:ℕ):ℝ) = x ^ 4
    rw [Real.rpow_natCast]
    exact habs x
  have heq : (∫ x : ℝ, |x|^(2*(2:ℝ)) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) =
      (∫ x : ℝ, |x|^(2*(2:ℝ)) ∂freeMeasure L u.val) + Rfield (L := L) 2 (by omega) κ (i u) := by
    have hfi := free_power_integrable (L := L) 2 (by norm_num) u
    have hfi' : Integrable (fun x : ℝ => x ^ (2*2)) (freeMeasure L u.val) := by rwa [hpow] at hfi
    have hsq := representative_hsq 2 u
    have hsq' : QuantumNLS.RiccatiSobolevE1.hsq L (2:ℕ) (fun n => QuantumNLS.Fourier.coeff L (i u).val n) ≠ ⊤ := by rw [hi]; exact hsq
    have h := finite_field_identity κ hκ 2 (by omega) (i u) hsq'
    rw [hi] at h
    have hfree := free_finite_moment u.val 2 hfi'
    have he := h.trans (congrArg (fun x => x + Rfield (L := L) 2 (by omega) κ (i u)) hfree.symm)
    rw [hpow]
    exact he
  linarith [le_abs_self (Rfield (L := L) 2 (by omega) κ (i u))]

#print axioms physical_one_bounded
#print axioms physical_two_bounded
end QuantumNLS.TerraMultiRound80EndpointBound
