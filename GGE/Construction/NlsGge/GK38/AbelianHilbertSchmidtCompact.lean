import NlsGge.Analysis.RegularizedDeterminant.ColumnsAndCompleteness
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! Generic actual real Hilbert--Schmidt to compact bridge for source Lemma14.6.
UNCOMPILED source preparation; actual P3 HS membership remains to be proved. -/
set_option autoImplicit false
open Filter Topology
namespace NlsGge.GK38.P3OperatorBridge
noncomputable section
open NlsGge.Analysis.RegularizedDeterminant
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem finiteRank_isCompact (T : E →L[ℝ] F) (hT : HilbertSchmidt.HasFiniteRank T) :
    IsCompactOperator T := by
  let _ : FiniteDimensional ℝ (LinearMap.range T.toLinearMap) := hT
  have hc : IsCompactOperator T.rangeRestrict :=
    isCompactOperator_of_locallyCompactSpace_dom T.rangeRestrict
  exact hc.clm_comp (LinearMap.range T.toLinearMap).subtypeL

theorem hilbertSchmidt_isCompact (T : E →L[ℝ] F) (hT : IsHilbertSchmidt T) :
    IsCompactOperator T := by
  let A : HilbertSchmidt E F := HilbertSchmidt.ofCLM T hT
  have hconv : Tendsto
      (fun S : Finset (basisIndex E) =>
        HilbertSchmidt.toCLM (HilbertSchmidt.finiteColumnApprox A S))
      atTop (𝓝 T) := by
    change Tendsto
      (fun S : Finset (basisIndex E) =>
        HilbertSchmidt.toCLM (HilbertSchmidt.finiteColumnApprox A S))
      atTop (𝓝 (HilbertSchmidt.toCLM A))
    exact (HilbertSchmidt.toCLMContinuous (E := E) (F := F)).continuous.tendsto A |>.comp
      (HilbertSchmidt.tendsto_finiteColumnApprox A)
  apply isCompactOperator_of_tendsto hconv
  exact Eventually.of_forall (fun S =>
    finiteRank_isCompact _ (HilbertSchmidt.finiteColumnApprox_finiteRank A S))

end
end NlsGge.GK38.P3OperatorBridge
