import QuantumNLS.LOCAL009R23Final
/-! integrator-authored trusted spec for LOCAL-009 RESET:B06:second-order (terra_review r187 FULL support): headline statement(s) copied verbatim from LOCAL009R23Final (QuantumNLS.LOCAL009R23Final). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
open Complex Set
open scoped InnerProductSpace
namespace QuantumNLS.L009Spec
open QuantumNLS.LOCAL009R23Final
open QuantumNLS.LOCAL009R23PhysicalInverse QuantumNLS.LOCAL009R23OperatorContour
  QuantumNLS.LOCAL009R23DiagonalAnalytic QuantumNLS.LOCAL009R23Vacuum
  QuantumNLS.LOCAL009R22LiteralScalar QuantumNLS.LOCAL009R22Assembly
  QuantumNLS.LOCAL009R22OperatorSupport QuantumNLS.BetheLabels
variable {L κ M ε : ℝ} [Fact (0 < L)] {N : ℕ}

set_option maxHeartbeats 8000000 in
theorem LOCAL_009_spec (hκ : 0 < κ) (hM : 0 < M) (hsmall : κ*L*M ≤ 1/1000000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ M →
      (∀ n : ℤ, ∀ N : ℕ, ε*N ≤ M →
        ‖(ε : ℂ) • occupationCount L κ ε hκ hε n N-approximation L κ M ε n N‖ ≤ C*ε^2 ∧
        ‖(ε : ℂ) • occupationCount L κ ε hκ hε n N-hermitianPart (approximation L κ M ε n N)‖ ≤ C*ε^2) ∧
      (⨆ n : ℤ, ⨆ N : {N : ℕ // ε*N ≤ M},
        ‖(ε : ℂ) • occupationCount L κ ε hκ hε n N.1-approximation L κ M ε n N.1‖) ≤ C*ε^2 ∧
      (⨆ n : ℤ, ⨆ N : {N : ℕ // ε*N ≤ M},
        ‖(ε : ℂ) • occupationCount L κ ε hκ hε n N.1-hermitianPart (approximation L κ M ε n N.1)‖) ≤ C*ε^2 := by
  exact QuantumNLS.LOCAL009R23Final.«LOCAL-009» hκ hM hsmall

end QuantumNLS.L009Spec
#print axioms QuantumNLS.L009Spec.LOCAL_009_spec
