import QuantumNLS.TerraMultiRound78UpperAssembly
import QuantumNLS.Reg010LowMomentReduction
import QuantumNLS.Reg010LowFinal
import QuantumNLS.TerraMultiRound64BaseCriterion

/-! Upper physical moments bootstrap to H¹ on every L² field. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound78UpperAssembly
namespace QuantumNLS.TerraMultiRound78UpperBootstrap

variable {L : ℝ} [Fact (0 < L)]

theorem higher_physical_moment_H1 (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 1 ≤ s)
    (hm : Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u)) :
    ∃ v : Hk L 1, v.val = u := by
  have h2 := (QuantumNLS.Reg010LowMomentReduction.lower_moment_integrable
    (PhysicalQuantumMeasure.measure hκ u) 2 (2*s) (by norm_num) (by linarith) hm).1
  have h2' : Integrable (fun x : ℝ => x^2) (PhysicalQuantumMeasure.measure hκ u) := by
    simpa only [Real.rpow_two, sq_abs] using h2
  have hsq := (QuantumNLS.TerraMultiRound64BaseCriterion.physical_second_iff_hsq L κ hκ u).mp h2'
  have hsq' : QuantumNLS.RiccatiSobolevE1.hsq L (1:ℝ)
      (fun n => QuantumNLS.Fourier.coeff L u n) ≠ ⊤ := by simpa only [Nat.cast_one] using hsq
  have hf := (QuantumNLS.Reg010LowFreeSobolev.free_power_integrable_iff_hsq u 1 (by norm_num)).mpr hsq'
  change ∃ v : H02 L ((1:ℕ):ℝ), v.val = u
  rw [show ((1:ℕ):ℝ) = (1:ℝ) by norm_num]
  exact (QuantumNLS.Reg010LowFreeSobolev.free_power_integrable_iff_H02 u 1 (by norm_num)).mp hf

theorem upper_characterization (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2) :
    Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u) ↔
      ∃ v : H02 L s, v.val = u := by
  constructor
  · intro hm
    obtain ⟨w, hw⟩ := higher_physical_moment_H1 κ hκ u s (le_of_lt hs1) hm
    have hm' : Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ w.val) := by
      rw [hw]; exact hm
    obtain ⟨v, hv⟩ := (upper_characterization_H1 κ hκ w s hs1 hs2).mp hm'
    exact ⟨v, hv.trans hw⟩
  · rintro ⟨v, hv⟩
    have hst : ((1:ℕ):ℝ) ≤ s := by simpa only [Nat.cast_one] using (le_of_lt hs1)
    let w : Hk L 1 := H02.mono hst v
    have hw : w.val = u := (QuantumNLS.Reg010LowFinal.H02_lower_val ((1:ℕ):ℝ) s hst v).trans hv
    have hm := (upper_characterization_H1 κ hκ w s hs1 hs2).mpr ⟨v, hv.trans hw.symm⟩
    rwa [hw] at hm

#print axioms higher_physical_moment_H1
#print axioms upper_characterization
end QuantumNLS.TerraMultiRound78UpperBootstrap
