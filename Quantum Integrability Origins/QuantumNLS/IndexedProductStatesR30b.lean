import QuantumNLS.Local014Main

/-! Actual product density matrices satisfy every initial-state hypothesis
of accepted LOCAL-014, including trace-norm one-body condensation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology MeasureTheory Complex
open scoped InnerProductSpace
namespace QuantumNLS.IndexedProductStatesR30b
open TensorCarrier KernelDefinition LocalPlacement Local014RealSymbol
  Local014OneBody Local014Main Local014StateLimits TraceClass Ext025A12Normal
  Ext025B11TracePairing Ext025B11TraceBasis
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def productDensity (u : H) (N : ℕ) : SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  InnerProductSpace.rankOne ℂ (prodVec N u) (prodVec N u)

theorem product_norm {u : H} (hu : ‖u‖ = 1) (N : ℕ) : ‖prodVec N u‖ = 1 := by
  change ‖htpow N u‖ = 1
  rw [norm_htpow,hu,one_pow]

theorem product_normal {u : H} (hu : ‖u‖ = 1) (N : ℕ) : IsNormalState (productDensity u N) := by
  refine ⟨InnerProductSpace.isPositive_rankOne_self _,
    lt_of_le_of_lt (Fidelity.traceNorm_rankOne_le _ _) ENNReal.ofReal_lt_top,?_⟩
  change trace (refBasis _) (InnerProductSpace.rankOne ℂ _ _) = 1
  rw [trace_rankOne,inner_self_eq_norm_sq_to_K,product_norm hu]
  norm_num

theorem product_oneBody_fidelity {u : H} (hu : ‖u‖ = 1) {N : ℕ} (hN : 1 ≤ N) :
    ⟪u, oneBody N (productDensity u N) u⟫_ℂ = 1 := by
  have hρ := product_normal hu N
  rw [inner_oneBody_eq hN hρ.1 hρ.2.1,toSym1_rankOne]
  change trace (refBasis _) (InnerProductSpace.rankOne ℂ _ _ * _) = 1
  rw [trace_rankOne_right]
  rw [RadiusBound.Q_eq_genericU_N_r]
  change inner ℂ (htpow N u : HilbertTensorPower ℂ H N)
    ((genericU_N_r N 1 hN (P u 1) ⟨htpow N u,htpow_mem_symSector N u⟩ : SymSector ℂ H N) :
      HilbertTensorPower ℂ H N) = 1
  rw [inner_genericU_N_r_product_of_unit N 1 hN _ u hu]
  exact kps_P_self hu

theorem product_oneBody_exact {u : H} (hu : ‖u‖ = 1) {N : ℕ} (hN : 1 ≤ N) :
    traceNorm (oneBody N (productDensity u N)-InnerProductSpace.rankOne ℂ u u) = 0 := by
  apply le_antisymm _ zero_le
  have hb := traceNorm_sub_rankOne_le (oneBody_isNormalState hN (product_normal hu N)) u hu
  rw [product_oneBody_fidelity hu hN] at hb
  simpa using hb

theorem product_condensation {u : H} (hu : ‖u‖ = 1) :
    Tendsto (fun N => traceNorm (oneBody N (productDensity u N)-InnerProductSpace.rankOne ℂ u u))
      atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (product_oneBody_exact hu hN).symm

end QuantumNLS.IndexedProductStatesR30b
#print axioms QuantumNLS.IndexedProductStatesR30b.product_normal
#print axioms QuantumNLS.IndexedProductStatesR30b.product_condensation
