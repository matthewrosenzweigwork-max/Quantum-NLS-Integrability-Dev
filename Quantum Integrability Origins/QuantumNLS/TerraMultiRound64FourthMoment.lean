import QuantumNLS.TerraMultiRound64SecondLimit
import QuantumNLS.TerraMultiRound62MomentTransfer

/-! At H¹, the fourth physical and free moments are finite simultaneously. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound59REG007
open QuantumNLS.TerraMultiRound59SignedCharges QuantumNLS.TerraMultiRound60Kernel
open QuantumNLS.TerraMultiRound64BaseCoefficient QuantumNLS.TerraMultiRound64SecondLimit
open QuantumNLS.TerraMultiRound62MomentTransfer
namespace QuantumNLS.TerraMultiRound64FourthMoment

theorem fourth_moment_transfer (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ)
    (u : L2T L) (hu : hsq L (1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ x : Ell2, ∃ ha0 : 0 ≤ ((1 : ℕ) : ℝ), fieldMap L (1 : ℕ) ha0 x = u ∧
      (Integrable (fun t : ℝ => t^4) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
        Integrable (fun t : ℝ => t^4) (freeMeasure L u)) ∧
      (Integrable (fun t : ℝ => t^4) (freeMeasure L u) →
        (∫ t : ℝ, t^4 ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) =
        (∫ t : ℝ, t^4 ∂(freeMeasure L u)) +
          retainedR (L := L) 2 (by omega) κ (physicalToHk (L := L) (2-1) x) 2) := by
  obtain ⟨x, ha0, hx, hlim⟩ := physical_fourth_regularized_limit L κ hκ u hu
  have hv : (physicalToHk (L := L) 1 x).val = u :=
    (physicalToHk_val_eq_fieldMap L 1 ha0 x).trans hx
  have hH := representative_oneH1 u (physicalToHk (L := L) 1 x) hv
  have hμ : Integrable (fun t : ℝ => t^(2*1)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
    rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas hκ u]
    simpa using (QuantumNLS.RDF8Main.root_H1_characterization hκ u).1.mp hH
  have hν := free_second_integrable u hH
  have ht := moment_transfer (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) (freeMeasure L u) 1
    (retainedR (L := L) 2 (by omega) κ (physicalToHk (L := L) (2-1) x) 2) hμ hν
    (hlim.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
  exact ⟨x, ha0, hx, by simpa using ht⟩

#print axioms fourth_moment_transfer
end QuantumNLS.TerraMultiRound64FourthMoment
