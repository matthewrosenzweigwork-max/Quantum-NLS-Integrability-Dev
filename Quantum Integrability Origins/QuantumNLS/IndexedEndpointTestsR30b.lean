import QuantumNLS.IndexedQuantumEndpointR30b
import QuantumNLS.IndexedProductStatesR30b

/-! Actual physical product-state tests return to their initial limits at
2pi for the corrected contour Hamiltonians. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology Complex
open scoped InnerProductSpace
namespace QuantumNLS.IndexedEndpointTestsR30b
open Ext025A12Trace
open TensorCarrier KernelDefinition LocalPlacement Local014OneBody Local014Main Local014StateLimits
  Local014RealSymbol Local014Heisenberg TraceClass Ext025A12Normal Ext025B11TracePairing
  Ext025B11TraceBasis IndexedProductStatesR30b IndexedQuantumEndpointR30b IndexedHermitianR30b
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem conjugation_bound (U X : H →L[ℂ] H) :
    ‖U*X*star U-X‖ ≤ ‖X‖*(‖U-1‖*(‖U-1‖+1)+‖U-1‖) := by
  have hid : U*X*star U-X = (U-1)*X*star U+X*(star U-1) := by noncomm_ring
  have hn : ‖U‖ ≤ ‖U-1‖+1 := by
    calc
      _ = ‖(U-1)+1‖ := by rw [sub_add_cancel]
      _ ≤ ‖U-1‖+‖(1 : H →L[ℂ] H)‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact ContinuousLinearMap.norm_id_le
  have hs : ‖star U-1‖ = ‖U-1‖ := by
    simpa only [star_sub,star_one] using (norm_star (U-1))
  rw [hid]
  calc
    _ ≤ ‖(U-1)*X*star U‖+‖X*(star U-1)‖ := norm_add_le _ _
    _ ≤ (‖U-1‖*‖X‖)*‖U‖+‖X‖*‖U-1‖ := by
      simpa only [norm_star,hs] using add_le_add
        ((norm_mul_le ((U-1)*X) (star U)).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le (U-1) X) (ContinuousLinearMap.opNorm_nonneg (star U))))
        (norm_mul_le X (star U-1))
    _ ≤ (‖U-1‖*‖X‖)*(‖U-1‖+1)+‖X‖*‖U-1‖ := by gcongr
    _ = _ := by ring

open PhysicalTensor IndexedCFCBindingR29b
variable {L κ : ℝ} [Fact (0 < L)]

def endpointTest (κ : ℝ) (n : ℤ) (u : L2T L) (N : ℕ) : ℂ :=
  if hN : 1 ≤ N then tr (productDensity u N *
    (opExp (endpointScalar N • hamiltonian (L := L) κ n N)*RadiusBound.Q N 1 hN (P u 1)*
      opExp ((-endpointScalar N) • hamiltonian (L := L) κ n N))) else 0

theorem endpointScalar_star (N : ℕ) : star (endpointScalar N) = -endpointScalar N := by
  simp [endpointScalar]

theorem endpoint_test_limit (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) (u : L2T L) (hu : ‖u‖ = 1) : Tendsto (endpointTest κ n u) atTop (𝓝 1) := by
  let δ : ℕ → ℝ := fun N => ‖opExp (endpointScalar N • hamiltonian (L := L) κ n N)-1‖
  have hd : Tendsto δ atTop (𝓝 0) := endpoint_norm_tendsto_zero hκ hs n
  have hb : Tendsto (fun N => ‖P u 1‖*(δ N*(δ N+1)+δ N)) atTop (𝓝 0) := by
    simpa using ((hd.mul (hd.add_const 1)).add hd).const_mul ‖P u 1‖
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hb
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [endpointTest,dite_eq_left hN]
  let U := opExp (endpointScalar N • hamiltonian (L := L) κ n N)
  let X := RadiusBound.Q N 1 hN (P u 1)
  have hstar : opExp ((-endpointScalar N) • hamiltonian (L := L) κ n N) = star U :=
    (star_opExp_cN (hamiltonian_selfAdjoint κ n N) _ (endpointScalar_star N)).symm
  rw [hstar]
  have hρ := product_normal hu N
  have htest : tr (productDensity u N*X) = 1 := by
    change tr (productDensity u N*RadiusBound.Q N 1 hN (P u 1)) = 1
    rw [← toSym1_rankOne,← inner_oneBody_eq hN hρ.1 hρ.2.1 u]
    exact product_oneBody_fidelity hu hN
  have htx : tr (productDensity u N*X) = ⟪prodVec N u,X (prodVec N u)⟫_ℂ :=
    trace_rankOne_right (refBasis _) X _ _
  have htu : tr (productDensity u N*(U*X*star U)) =
      ⟪prodVec N u,(U*X*star U) (prodVec N u)⟫_ℂ := trace_rankOne_right (refBasis _) _ _ _
  rw [htu,← htest,htx,← inner_sub_right,← sub_apply]
  calc
    _ ≤ ‖U*X*star U-X‖ := by
      apply (norm_inner_le_norm _ _).trans
      rw [product_norm hu N,one_mul]
      simpa only [product_norm hu N,mul_one] using (U*X*star U-X).le_opNorm (prodVec N u)
    _ ≤ ‖X‖*(δ N*(δ N+1)+δ N) := conjugation_bound U X
    _ ≤ ‖P u 1‖*(δ N*(δ N+1)+δ N) :=
      mul_le_mul_of_nonneg_right (RadiusBound.norm_Q_le N 1 hN _) (by dsimp [δ]; positivity)

end QuantumNLS.IndexedEndpointTestsR30b
#print axioms QuantumNLS.IndexedEndpointTestsR30b.endpoint_test_limit
