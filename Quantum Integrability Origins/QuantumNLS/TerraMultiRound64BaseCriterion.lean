import QuantumNLS.TerraMultiRound64FourthAllFields

/-! The accepted H¹ criterion in the same Fourier convention as higher orders. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.TerraMultiRound49SobolevBridge
open QuantumNLS.TerraMultiRound59REG007 QuantumNLS.TerraMultiRound64BaseCoefficient
open QuantumNLS.TerraMultiRound64FreeSobolev QuantumNLS.TerraMultiRound64SecondLimit
namespace QuantumNLS.TerraMultiRound64BaseCriterion

theorem physical_second_iff_hsq (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (u : L2T L) :
    Integrable (fun t : ℝ => t^2) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
      hsq L (1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ := by
  constructor
  · intro hp
    rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas hκ u] at hp
    have hH := (QuantumNLS.RDF8Main.root_H1_characterization hκ u).1.mpr hp
    exact (free_even_integrable_iff_hsq u 1).mp (free_second_integrable u hH)
  · intro hu
    obtain ⟨x, ha0, hx, _⟩ := physical_fourth_regularized_limit L κ hκ u hu
    have hv : (physicalToHk (L := L) 1 x).val = u :=
      (physicalToHk_val_eq_fieldMap L 1 ha0 x).trans hx
    have hH := representative_oneH1 u (physicalToHk (L := L) 1 x) hv
    rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas hκ u]
    exact (QuantumNLS.RDF8Main.root_H1_characterization hκ u).1.mp hH

#print axioms physical_second_iff_hsq
end QuantumNLS.TerraMultiRound64BaseCriterion
