import QuantumNLS.TerraMultiRound91MarginalContraction
import QuantumNLS.PhysicalTensor

/-! Exact contraction of unit pure-state trace distance to any tensor marginal. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.TraceClass
open QuantumNLS.TerraMultiRound91MarginalContraction
namespace QuantumNLS.TerraMultiRound91MarginalPure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem marginal_pure_contraction (N k : ℕ) (hk : k ≤ N)
    (v w : SymSector ℂ H N) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    traceNorm (reducedDensityN N k hk v.val - reducedDensityN N k hk w.val) ≤
      traceNorm (InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ w w) := by
  let e := (castHTP (𝕜 := ℂ) (E := H) (Nat.add_sub_cancel' hk).symm).trans
    (splitIsometry k (N-k))
  have hnv : ‖e v.val‖ = 1 := by rw [e.norm_map]; exact hv
  have hnw : ‖e w.val‖ = 1 := by rw [e.norm_map]; exact hw
  have hi : ⟪e v.val, e w.val⟫_ℂ = ⟪v, w⟫_ℂ := by rw [e.inner_map_map]; rfl
  have h := reduced_pure_contraction (e v.val) (e w.val)
  change traceNorm (reducedDensityN N k hk v.val - reducedDensityN N k hk w.val) ≤ _ at h
  refine h.trans_eq ?_
  rw [RankTwoTrace.traceNorm_unit_sub_eq _ _ hnv hnw,
    RankTwoTrace.traceNorm_unit_sub_eq _ _ hv hw, hi]

theorem unitary_marginal_contraction (N k : ℕ) (hk : k ≤ N)
    (v w : SymSector ℂ H N) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (U : SymSector ℂ H N ≃ₗᵢ[ℂ] SymSector ℂ H N) :
    traceNorm (reducedDensityN N k hk (U v).val - reducedDensityN N k hk (U w).val) ≤
      traceNorm (InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ w w) := by
  have huv : ‖U v‖ = 1 := by rw [U.norm_map, hv]
  have huw : ‖U w‖ = 1 := by rw [U.norm_map, hw]
  refine (marginal_pure_contraction N k hk (U v) (U w) huv huw).trans_eq ?_
  rw [RankTwoTrace.traceNorm_unit_sub_eq _ _ huv huw,
    RankTwoTrace.traceNorm_unit_sub_eq _ _ hv hw, U.inner_map_map]

#print axioms marginal_pure_contraction
#print axioms unitary_marginal_contraction
end QuantumNLS.TerraMultiRound91MarginalPure
