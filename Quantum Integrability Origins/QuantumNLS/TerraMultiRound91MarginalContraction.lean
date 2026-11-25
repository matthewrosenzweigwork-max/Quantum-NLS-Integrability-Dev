import QuantumNLS.Ext025A12PartialTrace
import QuantumNLS.RankTwoTrace

/-! Exact partial-trace contraction for differences of pure states. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.TraceClass QuantumNLS.TraceIdeal QuantumNLS.Ext025A12PartialTrace
open QuantumNLS.TensorCarrier QuantumNLS.Fidelity QuantumNLS.Ext025A12Trace
namespace QuantumNLS.TerraMultiRound91MarginalContraction
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

theorem reduced_pure_contraction (ψ φ : HilbertTensor ℂ X Y) :
    traceNorm (reducedDensity ψ - reducedDensity φ) ≤
      traceNorm (InnerProductSpace.rankOne ℂ ψ ψ - InnerProductSpace.rankOne ℂ φ φ) := by
  let A := InnerProductSpace.rankOne ℂ ψ ψ
  let B := InnerProductSpace.rankOne ℂ φ φ
  have hA : IsTraceClass A := (traceNorm_rankOne_le ψ ψ).trans_lt ENNReal.ofReal_lt_top
  have hB : IsTraceClass B := (traceNorm_rankOne_le φ φ).trans_lt ENNReal.ofReal_lt_top
  have hBneg : IsTraceClass ((-1 : ℂ) • B) := finite_smul _ hB
  have hadd : IsTraceClass (A + (-1 : ℂ) • B) := hA.add hBneg
  have he : partialTrace (A + (-1 : ℂ) • B) hadd = reducedDensity ψ - reducedDensity φ := by
    rw [partialTrace_add A ((-1 : ℂ) • B) hA hBneg, partialTrace_smul (-1) B hB]
    change partialTrace (InnerProductSpace.rankOne ℂ ψ ψ) hA + (-1 : ℂ) •
      partialTrace (InnerProductSpace.rankOne ℂ φ φ) hB = _
    rw [partialTrace_rankOne, partialTrace_rankOne]
    simp [sub_eq_add_neg]
  have ht := traceNorm_partialTrace_le (A + (-1 : ℂ) • B) hadd
  rw [he] at ht
  simpa only [neg_one_smul, sub_eq_add_neg] using ht

#print axioms reduced_pure_contraction
end QuantumNLS.TerraMultiRound91MarginalContraction
