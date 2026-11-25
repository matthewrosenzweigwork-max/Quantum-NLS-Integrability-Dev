import QuantumNLS.TerraMultiRound78UpperPrinted
import QuantumNLS.TerraMultiRound78UpperEquivalence
import QuantumNLS.Reg010LowFreeSobolev

/-! Upper-order characterization and literal formula on the H¹ carrier. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound78UpperPrinted QuantumNLS.TerraMultiRound78UpperEquivalence
namespace QuantumNLS.TerraMultiRound78UpperAssembly

variable {L : ℝ} [Fact (0 < L)]

theorem upper_characterization_H1 (κ : ℝ) (hκ : 0 < κ) (u : Hk L 1)
    (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2) :
    Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u.val) ↔
      ∃ v : H02 L s, v.val = u.val :=
  (physical_free_upper_iff κ hκ u s hs1 hs2).trans
    (QuantumNLS.Reg010LowFreeSobolev.free_power_integrable_iff_H02 u.val s (by linarith))

theorem upper_printed_of_physical_finite (κ : ℝ) (hκ : 0 < κ) (u : Hk L 1)
    (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2)
    (hm : Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u.val)) :
    (∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ u.val) =
      (∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L u.val) +
        (2 * Real.sin (Real.pi * (s-1)) / Real.pi) *
          QuantumNLS.TerraMultiRound75Correction.correction κ hκ s u :=
  physical_free_upper_printed κ hκ u s hs1 hs2 hm
    ((physical_free_upper_iff κ hκ u s hs1 hs2).mp hm)

#print axioms upper_characterization_H1
#print axioms upper_printed_of_physical_finite
end QuantumNLS.TerraMultiRound78UpperAssembly
