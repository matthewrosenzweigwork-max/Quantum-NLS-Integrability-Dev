import QuantumNLS.QuantumHighAngleTail

/-! The two projection errors in the R-B2E70586 quantum truncation bound.
This is a pure-state marginal estimate for an arbitrary unitary and does not
assert the spectral Markov bound or assume the final propagation theorem. -/
set_option autoImplicit false
noncomputable section
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor
namespace QuantumNLS.TerraMultiRound87Projection

/-- If a unit vector is δ-close to an energy-truncated unit vector, and a
unitary changes the latter's k-marginal by at most η, then it changes the
original k-marginal by at most `4δ + η`. -/
theorem marginal_projection_cost {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (N k : ℕ) (hk : k ≤ N)
    (v w : SymSector ℂ H N) (U : SymSector ℂ H N ≃ₗᵢ[ℂ] SymSector ℂ H N)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (δ η : ℝ) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hclose : ‖v - w‖ ≤ δ)
    (htail : TraceClass.traceNorm (reducedDensityN N k hk (U w).val -
      reducedDensityN N k hk w.val) ≤ ENNReal.ofReal η) :
    TraceClass.traceNorm (reducedDensityN N k hk (U v).val -
      reducedDensityN N k hk v.val) ≤ ENNReal.ofReal (4 * δ + η) := by
  have huv : ‖U v‖ = 1 := by rw [U.norm_map, hv]
  have huw : ‖U w‖ = 1 := by rw [U.norm_map, hw]
  have hUclose : ‖U v - U w‖ ≤ δ := by
    rw [← map_sub, U.norm_map]
    exact hclose
  have hfirst := MarginalPureState.traceNorm_reducedDensityN_sub_le N k hk (U v).val (U w).val
  have hlast := MarginalPureState.traceNorm_reducedDensityN_sub_le N k hk w.val v.val
  have hfirst' : TraceClass.traceNorm (reducedDensityN N k hk (U v).val -
      reducedDensityN N k hk (U w).val) ≤ ENNReal.ofReal (2 * δ) := by
    refine hfirst.trans (ENNReal.ofReal_le_ofReal ?_)
    change ‖U v - U w‖ * (‖U v‖ + ‖U w‖) ≤ 2 * δ
    rw [huv, huw]
    linarith
  have hlast' : TraceClass.traceNorm (reducedDensityN N k hk w.val -
      reducedDensityN N k hk v.val) ≤ ENNReal.ofReal (2 * δ) := by
    refine hlast.trans (ENNReal.ofReal_le_ofReal ?_)
    change ‖w - v‖ * (‖w‖ + ‖v‖) ≤ 2 * δ
    rw [hw, hv, norm_sub_rev]
    linarith
  have ht1 := QuantumHighAngleTail.marginal_triangle N k hk (U v) (U w) v
  have ht2 := QuantumHighAngleTail.marginal_triangle N k hk (U w) w v
  refine ht1.trans ((add_le_add le_rfl ht2).trans ?_)
  refine (add_le_add hfirst' (add_le_add htail hlast')).trans ?_
  rw [← ENNReal.ofReal_add hη (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply le_of_eq
  congr 1
  ring

#print axioms marginal_projection_cost
end QuantumNLS.TerraMultiRound87Projection
