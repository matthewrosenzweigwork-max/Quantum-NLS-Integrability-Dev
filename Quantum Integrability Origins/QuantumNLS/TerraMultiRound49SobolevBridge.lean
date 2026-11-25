import QuantumNLS.TerraMultiRound47PhysicalShift
import QuantumNLS.TranslatedCorrelation
import QuantumNLS.RiccatiExpansions

/-! Identify the weighted Fourier physical model with the REG-006 field
model, including the physical conjugate factor. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound49SobolevBridge
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.TerraMultiRound47PhysicalShift
open QuantumNLS.RiccatiExpansions QuantumNLS.ComplexifiedSobolevField

variable {L : ℝ} [Fact (0 < L)]

omit [Fact (0 < L)] in
theorem physical_memHs (a : ℝ) (u : Ell2) : MemHs L a (toField L a u) := by
  have h := (summable_sq u).congr (fun n => (wt_mul_norm_div_sq L a n (u n)).symm)
  simpa only [MemHs, sobolevWeight, wt, RiccatiSobolevE1.freq, toField] using h

def physicalToHk (k : ℕ) (u : Ell2) : Hk L k :=
  (fourierHs (L := L) (one_le_def002 L (Nat.cast_nonneg k))).symm
    (h02.ofMem (physical_memHs (L := L) (k : ℝ) u))

theorem physicalToHk_coeff (k : ℕ) (u : Ell2) (n : ℤ) :
    fourierL2 L (physicalToHk k u).val n = toField L (k : ℝ) u n := by
  have h := congrArg (fun x : h02 L (k : ℝ) => x.val n)
    ((fourierHs (L := L) (one_le_def002 L (Nat.cast_nonneg k))).apply_symm_apply
      (h02.ofMem (physical_memHs (L := L) (k : ℝ) u)))
  exact h

theorem physicalToHk_rep {k : ℕ} (hk : 1 ≤ k) (u : Ell2) (x : ℝ) :
    contRep hk (physicalToHk k u) (x : AddCircle L) = physRep L (k : ℝ) u x := by
  rw [contRep, sobolevEmbedding_apply, sobolevSeries_apply, toF1_val]
  rw [physRep_seriesRep]
  congr 1
  funext n
  exact physicalToHk_coeff k u n

theorem physicalToHk_conj_rep {k : ℕ} (hk : 1 ≤ k) (u : Ell2) (x : ℝ) :
    contRep hk (physicalToHk k (jEll u)) (x : AddCircle L) =
      starRingEnd ℂ (physRep L (k : ℝ) u x) := by
  rw [physicalToHk_rep, physRep_jEll]

#print axioms physical_memHs
#print axioms physicalToHk_coeff
#print axioms physicalToHk_rep
#print axioms physicalToHk_conj_rep
end QuantumNLS.TerraMultiRound49SobolevBridge
