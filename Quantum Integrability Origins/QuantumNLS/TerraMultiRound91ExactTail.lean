import QuantumNLS.TerraMultiRound91MarginalPure
import QuantumNLS.QuantumHighAngleTail
import QuantumNLS.TraceNormTopology

/-! Retain the exact pure-state projection trace distance through both
marginals in the high-angle triangle inequality. -/
set_option autoImplicit false
noncomputable section
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.TraceClass
open QuantumNLS.TerraMultiRound91MarginalPure
namespace QuantumNLS.TerraMultiRound91ExactTail
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exact_projection_cost (N k : ℕ) (hk : k ≤ N)
    (v w : SymSector ℂ H N) (U : SymSector ℂ H N ≃ₗᵢ[ℂ] SymSector ℂ H N)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (δ η : ℝ) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hclose : traceNorm (InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ w w) ≤
      ENNReal.ofReal δ)
    (htail : traceNorm (reducedDensityN N k hk (U w).val - reducedDensityN N k hk w.val) ≤
      ENNReal.ofReal η) :
    traceNorm (reducedDensityN N k hk (U v).val - reducedDensityN N k hk v.val) ≤
      ENNReal.ofReal (2 * δ + η) := by
  have hfirst := (unitary_marginal_contraction N k hk v w hv hw U).trans hclose
  have hreverse : traceNorm (InnerProductSpace.rankOne ℂ w w - InnerProductSpace.rankOne ℂ v v) =
      traceNorm (InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ w w) := by
    rw [← neg_sub, TraceNormTopology.traceNorm_neg]
  have hlast := (marginal_pure_contraction N k hk w v hw hv).trans (hreverse.le.trans hclose)
  have ht1 := QuantumHighAngleTail.marginal_triangle N k hk (U v) (U w) v
  have ht2 := QuantumHighAngleTail.marginal_triangle N k hk (U w) w v
  refine ht1.trans ((add_le_add le_rfl ht2).trans ?_)
  refine (add_le_add hfirst (add_le_add htail hlast)).trans ?_
  rw [← ENNReal.ofReal_add hη hδ, ← ENNReal.ofReal_add hδ (by positivity)]
  apply le_of_eq
  congr 1
  ring

#print axioms exact_projection_cost
end QuantumNLS.TerraMultiRound91ExactTail
