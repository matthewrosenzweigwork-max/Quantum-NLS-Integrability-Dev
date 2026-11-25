import QuantumNLS.TerraMultiRound91OccupationProjection
import QuantumNLS.TerraMultiRound89Orthogonal

/-! Normalized occupation-energy projection with the exact pure-state cost. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.PhysicalTensor QuantumNLS.TensorCarrier QuantumNLS.BetheCoefficientTransform
open QuantumNLS.HaarSpectralTail QuantumNLS.ProductEnergyPreparation QuantumNLS.ChargeEnergy
open QuantumNLS.TerraMultiRound91OccupationProjection
namespace QuantumNLS.TerraMultiRound91ProductCompression
variable {L : ℝ} [Fact (0 < L)]

theorem product_compression (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 0 < N)
    (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) (E : ℝ)
    (hE : 2 * energyH1 κ (u : AddCircle L → ℂ) < E)
    (P : HN L N →L[ℂ] HN L N)
    (hP : ∀ m, P (bas L hκ hN m) = mask L κ N E m • bas L hκ hN m) :
    ∃ w : HN L N, ‖w‖ = 1 ∧ P w = w ∧
      TraceClass.traceNorm (InnerProductSpace.rankOne ℂ (HighMomentsOps.wvec N u) (HighMomentsOps.wvec N u) -
        InnerProductSpace.rankOne ℂ w w) ≤
          ENNReal.ofReal (2 * Real.sqrt (energyH1 κ (u : AddCircle L → ℂ) / E)) := by
  have hC : 0 ≤ energyH1 κ (u : AddCircle L → ℂ) := by
    unfold energyH1
    apply add_nonneg
    · rw [kinetic_eq]
      exact tsum_nonneg (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    · exact mul_nonneg hκ.le (quartic_nonneg _)
  have hEpos : 0 < E := by linarith
  have hr : energyH1 κ (u : AddCircle L → ℂ) / E < 1 := by
    apply (div_lt_one hEpos).2
    linarith
  let v := HighMomentsOps.wvec N u
  have hv : ‖v‖ = 1 := by
    change ‖TensorCarrier.htpow N u‖ = 1
    rw [TensorCarrier.norm_htpow, hu, one_pow]
  have hd : ‖v - P v‖ ^ 2 ≤ energyH1 κ (u : AddCircle L → ℂ) / E :=
    occupation_product_defect κ hκ N hN u hu hH E hEpos P hP
  have hsmall : ‖v - P v‖ < 1 := by nlinarith [norm_nonneg (v - P v), sq_nonneg (‖v - P v‖ - 1)]
  obtain ⟨hid, hsa⟩ := TerraMultiRound89SpectralProjection.actual_mask_orthogonal hκ hN P hP
  obtain ⟨hw, hwP, heq⟩ := TerraMultiRound89Orthogonal.normalized_orthogonal_projection P hid hsa v hv hsmall
  refine ⟨(‖P v‖⁻¹ : ℝ) • P v, hw, hwP, ?_⟩
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le hd) (by norm_num))

#print axioms product_compression
end QuantumNLS.TerraMultiRound91ProductCompression
