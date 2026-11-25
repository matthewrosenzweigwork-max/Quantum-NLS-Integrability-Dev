import QuantumNLS.IndexedEndpointTestsR30b
import QuantumNLS.IndexedGlobalR27b

/-! Accepted LOCAL-014 instantiated with the actual contour Hamiltonians,
physical product states and actual indexed-mass flow. Exact occupation return
then forces classical unit-ray return, without a supplied ray hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology Complex
open scoped InnerProductSpace
namespace QuantumNLS.IndexedUnitRayR30b
open PhysicalTensor TensorCarrier KernelDefinition Local014Main Local014StateLimits Local014OneBody
  IndexedHermitianR30b IndexedPrincipalBindingR30b IndexedProductStatesR30b IndexedEndpointTestsR30b
  IndexedGlobalR27b RootMassInvolutionR8
attribute [local instance] InnerProductSpace.complexToReal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projector_symbol (u w : H) :
    kernelProductSymbol (P u 1) w = ((‖⟪u,w⟫_ℂ‖^2 : ℝ) : ℂ) := by
  rw [← toSym1_rankOne,kernelProductSymbol_toSym1,InnerProductSpace.rankOne_apply,inner_smul_right,
    ← inner_conj_symm w u,Complex.mul_conj,Complex.normSq_eq_norm_sq]

variable {L κ : ℝ} [Fact (0 < L)]

theorem actual_unit_ray (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) (u : L2T L) (hu : ‖u‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ flow hκ n (2*Real.pi) u = c • u := by
  have hn (t : ℝ) : ‖flow hκ n t u‖ = 1 := (flow_norm hκ n u t).trans hu
  have he := local014_analytic_egorov (H := L2T L) (hamiltonian (L := L) κ n)
    (hamiltonian_selfAdjoint (L := L) κ n) (hamiltonian_expansion (L := L) κ n) (hamiltonian_converges hκ hs n)
    (mass hκ n) (fun v _ => (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n v).differentiableAt)
    (fun v hv => (principal_symbol_actual_mass hκ hs n v hv).symm) hu
    (flow_initial hκ n u) (flow_derivative hκ n u) hn
    (productDensity u) (product_normal hu) (product_condensation hu)
  have ht : Tendsto (endpointTest κ n u) atTop
      (𝓝 (kernelProductSymbol (P u 1) (flow hκ n (2*Real.pi) u))) := by
    apply (he.2.1 (2*Real.pi) 1 (P u 1)).congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [endpointTest,dite_eq_left hN,IndexedQuantumEndpointR30b.endpointScalar]
    push_cast
    simp only [neg_smulL]
  have heq := tendsto_nhds_unique ht (endpoint_test_limit hκ hs n u hu)
  rw [projector_symbol] at heq
  have hsquare : ‖⟪u,flow hκ n (2*Real.pi) u⟫_ℂ‖^2 = 1 := by exact_mod_cast heq
  have hin : ‖⟪u,flow hκ n (2*Real.pi) u⟫_ℂ‖ = 1 := by nlinarith [norm_nonneg ⟪u,flow hκ n (2*Real.pi) u⟫_ℂ]
  obtain ⟨c,hc0,hc⟩ := (norm_inner_eq_norm_iff (𝕜 := ℂ) (x := u) (y := flow hκ n (2*Real.pi) u)
    (norm_ne_zero_iff.mp (by rw [hu]; norm_num))
    (norm_ne_zero_iff.mp (by rw [hn]; norm_num))).mp (by simpa only [hu,hn,one_mul] using hin)
  refine ⟨c,?_,hc⟩
  have h := congrArg norm hc
  simpa only [hn,norm_smul,hu,mul_one] using h.symm

end QuantumNLS.IndexedUnitRayR30b
#print axioms QuantumNLS.IndexedUnitRayR30b.actual_unit_ray
