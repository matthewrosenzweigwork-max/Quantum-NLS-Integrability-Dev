import QuantumNLS.TerraMultiRound56KernelSplit

/-! Absolute integrability of the unpaired physical vertex kernel. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound56VertexIntegrable
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound48TreeFubini
open QuantumNLS.TerraMultiRound48Orthant
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound56ProductSplit
open QuantumNLS.TerraMultiRound56KernelSplit
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev QuantumNLS.Fourier

variable {L : ℝ} [Fact (0 < L)]

/-- Absolute integrability holds for every spatial point, without division by
an outer field factor and without an extra hypothesis. -/
theorem vertexKernel_integrable {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (t : BinaryTree Unit) (Y : ℝ) (x : AddCircle L) :
    Integrable (fun time => vertexKernel hk u t Y time x)
      (Measure.pi (fun _ : Fin (2 * t.numNodes + 1) => volume.restrict (Ioi (0 : ℝ)))) := by
  unfold vertexKernel
  apply orthant_bounded_integrable _ _ (∏ i, cL L * ‖vertexField (L := L) k u t i‖)
  · apply continuous_finsetProd
    intro i hi
    unfold vertexValue
    apply (contRep hk _).continuous.comp
    have hc : Continuous (fun z : ℝ => (z : AddCircle L)) := by fun_prop
    have hs : Continuous (fun time : Fin (2 * t.numNodes + 1) → ℝ =>
        pathShift (finiteFactorPaths t) Y time ((finSuccEquiv _).symm (some i))) :=
      (continuous_apply ((finSuccEquiv _).symm (some i))).comp (pathShift_continuous (finiteFactorPaths t) Y)
    exact continuous_const.add (hc.comp hs)
  · intro time
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => norm_contRep_apply_le hk _ _)

#print axioms vertexKernel_integrable
end QuantumNLS.TerraMultiRound56VertexIntegrable
