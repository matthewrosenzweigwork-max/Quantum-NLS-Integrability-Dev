import QuantumNLS.IndexedContourAssemblyR30b

/-! The Hermitian contour Hamiltonians satisfy the radius-8 algebra and
representation hypotheses of LOCAL-014. Symbol identification and quantum
propagation are separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Filter Topology Complex
namespace QuantumNLS.IndexedHermitianR30b
open TensorCarrier KernelDefinition KernelConvergence LocalPlacement Local014RealSymbol
  IndexedCorrectedContourR30b IndexedCauchyKernelsR30b
  LOCAL009R22OperatorSupport
attribute [local instance] IndexedKernelContinuityR29b.kernelNormed
attribute [local instance] IndexedCauchyKernelsR30b.kernelComplexSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem represented_sa (A : ∀ N : ℕ, KernelList (H := H) N) (N : ℕ) :
    RadiusBound.represented (saList A N) = hermitianPart (RadiusBound.represented (A N)) := by
  have hadj : ContinuousLinearMap.adjoint (RadiusBound.represented (A N)) =
      ∑ p : Fin (N+1), RadiusBound.Q N p.1 (by omega) (ContinuousLinearMap.adjoint (A N p)) := by
    unfold RadiusBound.represented
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p _
    simp only [RadiusBound.Q_eq_genericU_N_r]
    exact GenericUAdjoint.adjoint_genericU_N_r _ _ _ _
  rw [hermitianPart,hadj]
  unfold RadiusBound.represented saList saKernel
  rw [← Finset.sum_add_distrib,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [RadiusBound.Q_eq_genericU_N_r,RootOverlapLimit.genericU_smul,RootOverlapLimit.genericU_add]

theorem hermitian_selfAdjoint (A : H →L[ℂ] H) : IsSelfAdjoint (hermitianPart A) := by
  change star ((1/2 : ℂ) • (A+star A)) = (1/2 : ℂ) • (A+star A)
  simp only [star_smul,star_add,star_star]
  norm_num
  rw [add_comm]

open PhysicalTensor IndexedContourAssemblyR30b IndexedCFCBindingR29b
  LOCAL009R23OperatorContour
variable {L κ : ℝ} [Fact (0 < L)]

def hamiltonianKernels (κ : ℝ) (n : ℤ) := saList (contourKernels (L := L) κ n)
def hamiltonianLimit (κ : ℝ) (n : ℤ) := saLim (contourLimit (L := L) κ n)
def hamiltonian (κ : ℝ) (n : ℤ) (N : ℕ) : LOCAL009R23PhysicalInverse.Sector L N →L[ℂ] LOCAL009R23PhysicalInverse.Sector L N :=
  hermitianPart (RadiusBound.represented (contourKernels (L := L) κ n N))

theorem hamiltonian_converges (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ) :
    ConvergesOnRadius 8 (hamiltonianKernels (L := L) κ n) (hamiltonianLimit (L := L) κ n) :=
  saList_converges (by norm_num) (contour_converges hκ hs n)

theorem hamiltonian_expansion (κ : ℝ) (n : ℤ) (N : ℕ) :
    RadiusBound.IsExpansion (hamiltonian (L := L) κ n N) (hamiltonianKernels (L := L) κ n N) :=
  (represented_sa (contourKernels (L := L) κ n) N).symm

theorem hamiltonian_selfAdjoint (κ : ℝ) (n : ℤ) (N : ℕ) :
    IsSelfAdjoint (hamiltonian (L := L) κ n N) := hermitian_selfAdjoint _

theorem hamiltonian_literal (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) :
    hamiltonian (L := L) κ n N = hermitianPart (approximation L κ 1 (eps N) n N) := by
  rw [hamiltonian,represented_contour hκ hs hN n]

end QuantumNLS.IndexedHermitianR30b
#print axioms QuantumNLS.IndexedHermitianR30b.hamiltonian_converges
#print axioms QuantumNLS.IndexedHermitianR30b.hamiltonian_expansion
#print axioms QuantumNLS.IndexedHermitianR30b.hamiltonian_literal
