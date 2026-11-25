import QuantumNLS.Ext025A8Propagation
import QuantumNLS.LinearTailPhysicalEvolution
import Mathlib.Data.Nat.Choose.Basic

/-! PROP-001, source bounded generator and autonomous classical equation.
Interaction index n denotes printed rank r=n+1 throughout. The placement
is the existing reciprocal-binomial average of zero-extended kernels. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Prop001
open TensorCarrier TensorPlacements KernelDefinition LinearTailPhysicalEvolution
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

abbrev Interactions (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  ∀ n : ℕ, BoundedSymmetricKernel H (n + 1)

def theta (N r : ℕ) : ℝ := (N.descFactorial r : ℝ) / (N : ℝ) ^ r

theorem theta_nonneg (N r : ℕ) : 0 ≤ theta N r := by
  unfold theta
  positivity

theorem theta_le_one (N r : ℕ) : theta N r ≤ 1 := by
  unfold theta
  apply div_le_one_of_le₀
  · exact_mod_cast Nat.descFactorial_le_pow N r
  · positivity

/-- H_N=N sum_{r=1}^N theta_{N,r} U_{N,r}(A_r), including the vacuum N=0. -/
def generator (A : Interactions H) (N : ℕ) : SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  (N : ℂ) • ∑ n : Fin N, (theta N (n.val + 1) : ℂ) •
    genericU_N_r N (n.val + 1) (Nat.succ_le_of_lt n.isLt) (A n.val)

theorem placement_selfAdjoint (A : Interactions H) (hA : ∀ n, IsSelfAdjoint (A n))
    (N : ℕ) (n : Fin N) :
    IsSelfAdjoint (genericU_N_r N (n.val + 1) (Nat.succ_le_of_lt n.isLt) (A n.val)) := by
  change ContinuousLinearMap.adjoint _ = _
  rw [GenericUAdjoint.adjoint_genericU_N_r, show (A n.val).adjoint = A n.val from hA n.val]

theorem generator_selfAdjoint (A : Interactions H) (hA : ∀ n, IsSelfAdjoint (A n))
    (N : ℕ) : IsSelfAdjoint (generator A N) := by
  unfold generator
  apply IsSelfAdjoint.smul (by simp [isSelfAdjoint_iff])
  exact isSelfAdjoint_sum (R := SymSector ℂ H N →L[ℂ] SymSector ℂ H N)
    (x := fun n : Fin N => (theta N (n.val + 1) : ℂ) •
      genericU_N_r N (n.val + 1) (Nat.succ_le_of_lt n.isLt) (A n.val))
    Finset.univ (fun n _ =>
    (show IsSelfAdjoint (theta N (n.val + 1) : ℂ) from by
      simp [isSelfAdjoint_iff]).smul (placement_selfAdjoint A hA N n))

theorem generator_norm_le (A : Interactions H) (N : ℕ) :
    ‖generator A N‖ ≤ (N : ℝ) * ∑ n : Fin N, ‖A n.val‖ := by
  unfold generator
  calc
    _ ≤ ‖(N : ℂ)‖ * ‖∑ n : Fin N, (theta N (n.val + 1) : ℂ) •
        genericU_N_r N (n.val + 1) (Nat.succ_le_of_lt n.isLt) (A n.val)‖ :=
      ContinuousLinearMap.opNorm_smul_le (N : ℂ) (∑ n : Fin N, (theta N (n.val + 1) : ℂ) •
        genericU_N_r N (n.val + 1) (Nat.succ_le_of_lt n.isLt) (A n.val))
    _ ≤ (N : ℝ) * ∑ n : Fin N, ‖A n.val‖ := by
      rw [Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      refine (norm_sum_le Finset.univ (fun n : Fin N => (theta N (n.val + 1) : ℂ) •
        genericU_N_r N (n.val + 1) (Nat.succ_le_of_lt n.isLt) (A n.val))).trans
          (Finset.sum_le_sum fun n _ => ?_)
      refine (ContinuousLinearMap.opNorm_smul_le (theta N (n.val + 1) : ℂ)
        (genericU_N_r N (n.val + 1) (Nat.succ_le_of_lt n.isLt) (A n.val))).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (theta_nonneg _ _)]
      exact (mul_le_mul_of_nonneg_left
        (norm_genericU_N_r_le N _ (Nat.succ_le_of_lt n.isLt) (A n.val))
          (theta_nonneg _ _)).trans
        (mul_le_of_le_one_left (norm_nonneg (A n.val)) (theta_le_one _ _))

def productVector (N : ℕ) (u : H) : SymSector ℂ H N :=
  ⟨htpow N u, htpow_mem_symSector N u⟩

omit [CompleteSpace H] in
theorem productVector_norm (N : ℕ) (u : H) : ‖productVector N u‖ = ‖u‖ ^ N :=
  norm_htpow N u

def quantumEvolution (A : Interactions H) (N : ℕ) (t : ℝ) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N := evolution (generator A N) t

theorem quantumEvolution_norm (A : Interactions H) (hA : ∀ n, IsSelfAdjoint (A n))
    (N : ℕ) (t : ℝ) (ψ : SymSector ℂ H N) :
    ‖quantumEvolution A N t ψ‖ = ‖ψ‖ :=
  evolution_norm (generator_selfAdjoint A hA N) t ψ

theorem quantumEvolution_derivative (A : Interactions H) (N : ℕ)
    (ψ : SymSector ℂ H N) (t : ℝ) :
    HasDerivAt (fun s => quantumEvolution A N s ψ)
      ((-Complex.I) • generator A N (quantumEvolution A N t ψ)) t :=
  hasDerivAt_evolution (generator A N) ψ t

/-- Literal autonomous classical clause, with both printed summability
hypotheses. The solution is constructed using the frozen GP-04 binding. -/
theorem classical (A : Interactions H) (hA : ∀ n, IsSelfAdjoint (A n))
    {a : ℝ} (ha : 0 < a)
    (_hcubic : Summable (fun n => ((n + 1 : ℕ) : ℝ) ^ 3 * ‖A n‖))
    (hexp : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n)))
    {u : H} (hu : ‖u‖ = 1) :
    ∃ α : ℝ → H, α 0 = u ∧ ContDiff ℝ 1 α ∧
      (∀ t, ‖α t‖ = 1 ∧ HasDerivAt α (Ext025A8.sourceHartreeField A (α t)) t) ∧
      (∀ β : ℝ → H, β 0 = u →
        (∀ t, ‖β t‖ = 1 ∧ HasDerivAt β (Ext025A8.sourceHartreeField A (β t)) t) → β = α) :=
  Ext025A8.prop001_application A hA ha hexp hu

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.theta_nonneg
#print axioms QuantumNLS.Prop001.theta_le_one
#print axioms QuantumNLS.Prop001.generator
#print axioms QuantumNLS.Prop001.placement_selfAdjoint
#print axioms QuantumNLS.Prop001.generator_selfAdjoint
#print axioms QuantumNLS.Prop001.generator_norm_le
#print axioms QuantumNLS.Prop001.productVector_norm
#print axioms QuantumNLS.Prop001.quantumEvolution_norm
#print axioms QuantumNLS.Prop001.quantumEvolution_derivative
#print axioms QuantumNLS.Prop001.classical
