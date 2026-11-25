import QuantumNLS.IndexedOccupationLimitR30b
import QuantumNLS.IndexedQuantumR27b
import QuantumNLS.IndexedCFCBindingR29b
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Product-state expectations of the actual normalized occupation operator.
The limiting scalar is the actual indexed mass, by the accepted occupation
limit. No principal-symbol equality is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology MeasureTheory Complex
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.IndexedOccupationExpectationR30b
open LOCAL009R22Assembly
open PhysicalTensor TensorCarrier BetheCoefficientTransform KernelDefinition
  IndexedOccupationLimitR30b IndexedCFCBindingR29b LOCAL009R23PhysicalInverse
  LOCAL009R23Final BulkResponseActual EmpiricalRapidity RootOccupationLimit BetheLabels
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem diagonal_expectation (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H)
    (a : ι → ℝ) (he : ∀ i, A (b i) = (a i : ℂ) • b i) (x : H) :
    ⟪x,A x⟫_ℂ = ∑' i, (a i : ℂ)*((‖⟪b i,x⟫_ℂ‖^2 : ℝ) : ℂ) := by
  have hh := ((b.hasSum_repr x).mapL A).mapL (innerSL ℂ x)
  simp only [innerSL_apply_apply] at hh
  rw [← hh.tsum_eq]
  apply tsum_congr
  intro i
  simp only [map_smul,he,HilbertBasis.repr_apply_apply,smul_smul,inner_smul_right]
  have hconj : ⟪x,b i⟫_ℂ = conj ⟪b i,x⟫_ℂ := (inner_conj_symm x (b i)).symm
  rw [hconj]
  calc
    _ = (a i : ℂ)*(⟪b i,x⟫_ℂ*conj ⟪b i,x⟫_ℂ) := by ring
    _ = _ := by rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]

variable {L κ : ℝ} [Fact (0 < L)]

theorem basis_eq (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) :
    basis (L := L) hκ (eps_pos hN) hN = physBasis L hκ N := by
  have he : κ*eps N*(N : ℝ) = κ := by rw [mul_assoc,eps_budget hN,mul_one]
  unfold basis LOCAL009Round50Diagonalization.physicalBetheBasis physBasis
  rw [dite_eq_left (show 1 ≤ N by omega)]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Exact finite-sector product expectation; the arbitrary vacuum convention
is irrelevant to all limiting statements. -/
theorem occupation_expectation (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (u : L2T L) (hu : ‖u‖ = 1) (n : ℤ) :
    ⟪productVec L N u, ((eps N : ℂ) • occupationCount L κ (eps N) hκ (eps_pos hN) n N)
      (productVec L N u)⟫_ℂ =
      (((∫ m : MArr N, (m.1 n : ℝ)/(N : ℝ) ∂(bornMeasure (physBasis L hκ N) u hu)) : ℝ) : ℂ) := by
  have hb (m : MArr N) : |(m.1 n : ℝ)/(N : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity : (0 : ℝ) < N)).mpr (by exact_mod_cast multiplicity_le m n)
  have hi := (integrable_of_bdd (bornMeasure (physBasis L hκ N) u hu)
    (fun m => (m.1 n : ℝ)/(N : ℝ)) 1 hb).ofReal (𝕜 := ℂ)
  have he (m : MArr N) : ((eps N : ℂ) • occupationCount L κ (eps N) hκ (eps_pos hN) n N)
      (physBasis L hκ N m) = (((m.1 n : ℝ)/(N : ℝ) : ℝ) : ℂ) • physBasis L hκ N m := by
    rw [← basis_eq hκ hN,smul_apply,occupationCount_eigen hκ (eps_pos hN) hN,smul_smul]
    congr 1
    unfold eps
    push_cast
    ring
  have hsum := PMF.integral_eq_tsum (bornPMF (physBasis L hκ N) u hu)
    (fun m : MArr N => (((m.1 n : ℝ)/(N : ℝ) : ℝ) : ℂ)) hi
  calc
    ⟪productVec L N u, ((eps N : ℂ) • occupationCount L κ (eps N) hκ (eps_pos hN) n N)
      (productVec L N u)⟫_ℂ =
        ∑' m : MArr N, (((m.1 n : ℝ)/(N : ℝ) : ℝ) : ℂ)*
          ((‖⟪physBasis L hκ N m,productVec L N u⟫_ℂ‖^2 : ℝ) : ℂ) :=
      diagonal_expectation (physBasis L hκ N) _ _ he _
    _ = ∑' m : MArr N, (bornPMF (physBasis L hκ N) u hu m).toReal •
        (((m.1 n : ℝ)/(N : ℝ) : ℝ) : ℂ) := by
      apply tsum_congr
      intro m
      rw [bornPMF_apply,ENNReal.toReal_ofReal (bornLaw_nonneg _ _ _)]
      simp only [bornLaw,Complex.real_smul]
      ring
    _ = ∫ m : MArr N, (((m.1 n : ℝ)/(N : ℝ) : ℝ) : ℂ)
        ∂(bornMeasure (physBasis L hκ N) u hu) := hsum.symm
    _ = (((∫ m : MArr N, (m.1 n : ℝ)/(N : ℝ)
      ∂(bornMeasure (physBasis L hκ N) u hu)) : ℝ) : ℂ) := integral_complex_ofReal

end QuantumNLS.IndexedOccupationExpectationR30b
#print axioms QuantumNLS.IndexedOccupationExpectationR30b.diagonal_expectation
#print axioms QuantumNLS.IndexedOccupationExpectationR30b.basis_eq
#print axioms QuantumNLS.IndexedOccupationExpectationR30b.occupation_expectation
