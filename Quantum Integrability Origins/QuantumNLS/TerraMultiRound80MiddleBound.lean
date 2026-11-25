import QuantumNLS.TerraMultiRound80FreeBound
import QuantumNLS.TerraMultiRound78LowContinuity

/-! Uniform physical power moments on bounded H^s sets for 1/2 ≤ s < 1. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.FreeLimit
open QuantumNLS.Reg010LowBasic QuantumNLS.Reg010LowCorrection QuantumNLS.Reg010LowL4Space QuantumNLS.Reg010LowL4Correction
open QuantumNLS.Reg010LowEmbeddingMap QuantumNLS.TerraMultiRound77FreeContinuity
open QuantumNLS.TerraMultiRound77YCorrection QuantumNLS.TerraMultiRound77LowEquivalence
open QuantumNLS.TerraMultiRound80FreeBound
namespace QuantumNLS.TerraMultiRound80MiddleBound
variable {L : ℝ} [Fact (0 < L)]

theorem middle_physical_power_bounded (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : (1:ℝ)/2 ≤ s) (hs1 : s < 1) (B : Set (H02 L s)) (hB : Bornology.IsBounded B) :
    ∃ M : ℝ, ∀ u ∈ B, (∫ x : ℝ, |x|^(2*s) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) ≤ M := by
  have hthird : (1:ℝ)/3 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  let i : H02 L s →L[ℂ] L4T L := embeddingH02.comp (H02.mono hthird)
  have hi (u : H02 L s) : toL2 (i u) = u.val := by
    change toL2 (embeddingH02 (H02.mono hthird u)) = u.val
    rw [embeddingH02_toL2]
    exact QuantumNLS.Reg010LowFinal.H02_lower_val (1/3) s hthird u
  have hA : Bornology.IsBounded (i '' B) := i.lipschitz.isBounded_image hB
  obtain ⟨C, hC, hint, hc⟩ := L4_correction_majorant κ hκ (i '' B) hA s hspos hs1
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp hB
  let J : ℝ := ∫ Y in Ioi 0, C * L4Majorant s Y
  let A : ℝ := 2 / (∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1)
  refine ⟨(max K 0)^2 + |A| * J, ?_⟩
  intro u hu
  have hR : |∫ Y in Ioi 0, Y ^ (2*s-3) * correction κ hκ u.val Y| ≤ J := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hint
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    simpa only [Real.norm_eq_abs, hi] using hc (i u) ⟨u, hu, rfl⟩ Y hY
  have hf := free_power_le_sobolev_norm s hspos.le u
  have hK2 : ‖u‖^2 ≤ (max K 0)^2 := pow_le_pow_left₀ (norm_nonneg _) ((hK u hu).trans (le_max_left _ _)) 2
  have hfi := free_power_integrable s hspos.le u
  have hfi' : Integrable (fun x : ℝ => |x|^(2*s)) (freeMeasure L (toL2 (i u))) := by rw [hi]; exact hfi
  have hmi := (physical_free_moment_iff_L4 hκ (i u) s hspos hs1).mpr hfi'
  have hid := physical_free_Y_correction hκ (toL2 (i u)) s hspos hs1 hmi hfi'
  rw [hi] at hid
  have hb : A * (∫ Y in Ioi 0, Y ^ (2*s-3) * correction κ hκ u.val Y) ≤ |A| * J := by
    calc
      _ ≤ |A * (∫ Y in Ioi 0, Y ^ (2*s-3) * correction κ hκ u.val Y)| := le_abs_self _
      _ = |A| * |∫ Y in Ioi 0, Y ^ (2*s-3) * correction κ hκ u.val Y| := abs_mul _ _
      _ ≤ |A| * J := mul_le_mul_of_nonneg_left hR (abs_nonneg _)
  change (∫ x : ℝ, |x|^(2*s) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) -
    (∫ x : ℝ, |x|^(2*s) ∂freeMeasure L u.val) = A * _ at hid
  linarith

#print axioms middle_physical_power_bounded
end QuantumNLS.TerraMultiRound80MiddleBound
