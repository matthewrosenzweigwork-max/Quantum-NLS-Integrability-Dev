import QuantumNLS.TerraMultiRound80FreeBound
import QuantumNLS.TerraMultiRound78UpperContinuity

/-! Uniform upper physical power moment bounds on bounded H^s sets. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.FreeLimit QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound77FreeContinuity QuantumNLS.TerraMultiRound80FreeBound
open QuantumNLS.TerraMultiRound75Correction QuantumNLS.TerraMultiRound78UpperEquivalence QuantumNLS.TerraMultiRound78UpperPhysical
namespace QuantumNLS.TerraMultiRound80UpperBound
variable {L : ℝ} [Fact (0 < L)]

theorem upper_physical_power_bounded (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs1 : 1 < s) (hs2 : s < 2) (B : Set (H02 L s)) (hB : Bornology.IsBounded B) :
    ∃ M : ℝ, ∀ u ∈ B, (∫ x : ℝ, |x|^(2*s) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) ≤ M := by
  have hst : ((1:ℕ):ℝ) ≤ s := by simpa only [Nat.cast_one] using (le_of_lt hs1)
  let i : H02 L s →L[ℂ] Hk L 1 := H02.mono hst
  have hi (u : H02 L s) : (i u).val = u.val :=
    QuantumNLS.Reg010LowFinal.H02_lower_val ((1:ℕ):ℝ) s hst u
  have hA : Bornology.IsBounded (i '' B) := i.lipschitz.isBounded_image hB
  obtain ⟨J, hJ⟩ := correction_bounded κ hκ s hs1 hs2 (i '' B) hA
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp hB
  let A : ℝ := 2 / (∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1)
  refine ⟨(max K 0)^2 + |A| * J, ?_⟩
  intro u hu
  have hR : |correction κ hκ s (i u)| ≤ J := hJ (i u) ⟨u, hu, rfl⟩
  have hf := free_power_le_sobolev_norm s (by linarith) u
  have hK2 : ‖u‖^2 ≤ (max K 0)^2 := pow_le_pow_left₀ (norm_nonneg _) ((hK u hu).trans (le_max_left _ _)) 2
  have hfi := free_power_integrable s (by linarith) u
  have hfi' : Integrable (fun x : ℝ => |x|^(2*s)) (freeMeasure L (i u).val) := by rw [hi]; exact hfi
  have hmi := (physical_free_upper_iff κ hκ (i u) s hs1 hs2).mpr hfi'
  have hid := physical_free_upper_finite κ hκ (i u) s hs1 hs2 hmi hfi'
  rw [hi] at hid
  have hb : A * correction κ hκ s (i u) ≤ |A| * J := by
    calc
      _ ≤ |A * correction κ hκ s (i u)| := le_abs_self _
      _ = |A| * |correction κ hκ s (i u)| := abs_mul _ _
      _ ≤ |A| * J := mul_le_mul_of_nonneg_left hR (abs_nonneg _)
  change (∫ x : ℝ, |x|^(2*s) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) -
    (∫ x : ℝ, |x|^(2*s) ∂freeMeasure L u.val) = A * _ at hid
  linarith

#print axioms upper_physical_power_bounded
end QuantumNLS.TerraMultiRound80UpperBound
