import QuantumNLS.IndexedHermitianR30b
import QuantumNLS.IndexedOccupationExpectationR30b

/-! Identification of the actual Hermitian contour's principal symbol on
unit physical profiles, by exact occupation comparison and product limits. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology MeasureTheory Complex
open scoped InnerProductSpace
namespace QuantumNLS.IndexedPrincipalBindingR30b
open BetheCoefficientTransform LOCAL009R22LiteralScalar
open PhysicalTensor TensorCarrier KernelDefinition KernelConvergence LocalPlacement Local014RealSymbol
  IndexedHermitianR30b IndexedCFCBindingR29b IndexedContourBoundsR29b IndexedOccupationLimitR30b
  IndexedOccupationExpectationR30b LOCAL009R23PhysicalInverse LOCAL009R23Final
  LOCAL009R22Assembly LOCAL009R22OperatorSupport
attribute [local instance] IndexedKernelContinuityR29b.kernelNormed
attribute [local instance] IndexedCauchyKernelsR30b.kernelComplexSpace
variable {L κ : ℝ} [Fact (0 < L)]

def normalizedOccupation (hκ : 0 < κ) (n : ℤ) (N : ℕ) : Sector L N →L[ℂ] Sector L N :=
  if hN : 0 < N then (eps N : ℂ) • occupationCount L κ (eps N) hκ (eps_pos hN) n N else 0

theorem normalized_expectation_limit (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (n : ℤ) :
    Tendsto (fun N : ℕ => ⟪productVec L N u, normalizedOccupation hκ n N (productVec L N u)⟫_ℂ)
      atTop (𝓝 (((RootIndexedMasses.masses hκ u).1 n : ℝ) : ℂ)) := by
  have ht := Complex.continuous_ofReal.tendsto _ |>.comp (component_limit hκ u hu n)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [normalizedOccupation,dite_eq_left hN]
  exact (occupation_expectation hκ hN u hu n).symm

theorem contour_occupation_bound (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) :
    ‖hamiltonian (L := L) κ n N-normalizedOccupation hκ n N‖ ≤ scalarConstant κ L 1*(eps N)^2 := by
  rw [hamiltonian_literal hκ hs hN,normalizedOccupation,dite_eq_left hN,norm_sub_rev]
  exact (positive_sector_bound hκ (by norm_num : (0 : ℝ) < 1)
    (show κ*L*1 ≤ 1/1000000 by nlinarith) hN (eps_pos hN) (eps_le_one hN)
    (by rw [eps_budget hN]) n).2

theorem principal_symbol_actual_mass (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) (u : L2T L) (hu : ‖u‖ = 1) :
    symbol (hamiltonianLimit (L := L) κ n) u = (((RootIndexedMasses.masses hκ u).1 n : ℝ) : ℂ) := by
  have hrep (N : ℕ) : RadiusBound.represented (hamiltonianKernels (L := L) κ n N) =
      hamiltonian (L := L) κ n N := (hamiltonian_expansion κ n N).symm
  have hp : Tendsto (fun N => ⟪prodVec N u,hamiltonian (L := L) κ n N (prodVec N u)⟫_ℂ)
      atTop (𝓝 (symbol (hamiltonianLimit (L := L) κ n) u)) := by
    simpa only [hrep] using tendsto_expect (by norm_num : (1 : ℝ) < 8)
      (hamiltonian_converges hκ hs n) u hu
  have hq := normalized_expectation_limit hκ u hu n
  have hn (N : ℕ) : ‖productVec L N u‖ = 1 := by
    change ‖htpow N u‖ = 1
    rw [norm_htpow,hu,one_pow]
  have hd : Tendsto (fun N => ‖⟪productVec L N u,
      ((hamiltonian (L := L) κ n N-normalizedOccupation hκ n N) : Sector L N →L[ℂ] Sector L N) (productVec L N u)⟫_ℂ‖)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (show Tendsto (fun N => scalarConstant κ L 1*(eps N)^2) atTop (𝓝 0) from by
        simpa using (eps_tendsto_zero.pow 2).const_mul (scalarConstant κ L 1))
    filter_upwards [eventually_gt_atTop 0] with N hN
    calc
      _ ≤ ‖hamiltonian (L := L) κ n N-normalizedOccupation hκ n N‖ := by
        apply (norm_inner_le_norm _ _).trans
        rw [hn N,one_mul]
        simpa only [hn N,mul_one] using
          ((hamiltonian (L := L) κ n N-normalizedOccupation hκ n N) : Sector L N →L[ℂ] Sector L N).le_opNorm (productVec L N u)
      _ ≤ _ := contour_occupation_bound hκ hs hN n
  have hd' : Tendsto (fun N => ⟪productVec L N u,hamiltonian (L := L) κ n N (productVec L N u)⟫_ℂ-
      ⟪productVec L N u,normalizedOccupation hκ n N (productVec L N u)⟫_ℂ) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [sub_apply,inner_sub_right] using hd
  have hr := hd'.add hq
  simp only [sub_add_cancel,zero_add] at hr
  exact tendsto_nhds_unique hp hr

end QuantumNLS.IndexedPrincipalBindingR30b
#print axioms QuantumNLS.IndexedPrincipalBindingR30b.principal_symbol_actual_mass
