import QuantumNLS.TerraMultiRound80FreeBound
import QuantumNLS.TerraMultiRound77MomentContinuity

/-! Uniform physical power moment bounds on bounded H^s sets for s < 1/2. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.FreeLimit
open QuantumNLS.Reg010LowBasic QuantumNLS.Reg010LowCorrection
open QuantumNLS.TerraMultiRound77FreeContinuity QuantumNLS.TerraMultiRound77YCorrection
open QuantumNLS.TerraMultiRound77LowEquivalence QuantumNLS.TerraMultiRound80FreeBound
namespace QuantumNLS.TerraMultiRound80LowBound
variable {L : ℝ} [Fact (0 < L)]

theorem low_physical_power_bounded (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1/2) (B : Set (H02 L s)) (hB : Bornology.IsBounded B) :
    ∃ M : ℝ, ∀ u ∈ B, (∫ x : ℝ, |x|^(2*s) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) ≤ M := by
  let i : H02 L s →L[ℂ] L2T L := H02.toL2 hs0.le
  have hi (u : H02 L s) : i u = u.val := rfl
  have hA : Bornology.IsBounded (i '' B) := i.lipschitz.isBounded_image hB
  obtain ⟨C, hC, hint, hc⟩ := low_correction_majorant κ hκ (i '' B) hA s hs0 hs1
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp hB
  let J : ℝ := ∫ Y in Ioi 0, C * lowMajorant s Y
  let A : ℝ := 2 / (∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1)
  refine ⟨(max K 0)^2 + |A| * J, ?_⟩
  intro u hu
  have hR : |∫ Y in Ioi 0, Y ^ (2*s-3) * correction κ hκ u.val Y| ≤ J := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hint
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    simpa only [Real.norm_eq_abs, hi] using hc (i u) ⟨u, hu, rfl⟩ Y hY
  have hf := free_power_le_sobolev_norm s hs0.le u
  have hK2 : ‖u‖^2 ≤ (max K 0)^2 := pow_le_pow_left₀ (norm_nonneg _) ((hK u hu).trans (le_max_left _ _)) 2
  have hfi := free_power_integrable s hs0.le u
  have hmi := (physical_free_moment_iff_L2 hκ u.val s hs0 hs1).mpr hfi
  have hid := physical_free_Y_correction hκ u.val s hs0 (by linarith) hmi hfi
  have hb : A * (∫ Y in Ioi 0, Y ^ (2*s-3) * correction κ hκ u.val Y) ≤ |A| * J := by
    calc
      _ ≤ |A * (∫ Y in Ioi 0, Y ^ (2*s-3) * correction κ hκ u.val Y)| := le_abs_self _
      _ = |A| * |∫ Y in Ioi 0, Y ^ (2*s-3) * correction κ hκ u.val Y| := abs_mul _ _
      _ ≤ |A| * J := mul_le_mul_of_nonneg_left hR (abs_nonneg _)
  change (∫ x : ℝ, |x|^(2*s) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) -
    (∫ x : ℝ, |x|^(2*s) ∂freeMeasure L u.val) = A * _ at hid
  linarith

#print axioms low_physical_power_bounded
end QuantumNLS.TerraMultiRound80LowBound
