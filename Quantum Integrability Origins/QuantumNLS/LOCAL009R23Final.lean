import QuantumNLS.LOCAL009R23Vacuum

/-! LOCAL-009: the printed transfer-only operator contour, the exact Bethe
occupation count, vacuum, and both uniform second-order operator bounds. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
open Complex Set
open scoped InnerProductSpace
namespace QuantumNLS.LOCAL009R23Final
open QuantumNLS.LOCAL009R23PhysicalInverse QuantumNLS.LOCAL009R23OperatorContour
  QuantumNLS.LOCAL009R23DiagonalAnalytic QuantumNLS.LOCAL009R23Vacuum
  QuantumNLS.LOCAL009R22LiteralScalar QuantumNLS.LOCAL009R22Assembly
  QuantumNLS.LOCAL009R22OperatorSupport QuantumNLS.BetheLabels

theorem zero_sector_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (ε C : ℝ) (hC : 0 ≤ C) :
    ‖(ε : ℂ) • (0 : H →L[ℂ] H)-0‖ ≤ C*ε^2 ∧
    ‖(ε : ℂ) • (0 : H →L[ℂ] H)-hermitianPart (0 : H →L[ℂ] H)‖ ≤ C*ε^2 := by
  constructor <;> simpa [hermitianPart] using mul_nonneg hC (sq_nonneg ε)

variable {L κ M ε : ℝ} [Fact (0 < L)] {N : ℕ}

/-- Exact integer occupation operator in the complete repulsive Bethe basis.
The zero-particle sector has zero occupation count. -/
def occupationCount (L κ ε : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (hε : 0 < ε)
    (n : ℤ) (N : ℕ) : Sector L N →L[ℂ] Sector L N :=
  if hN : 0 < N then diagonal (basis hκ hε hN) (fun m => (m.1 n : ℂ)) else 0

theorem occupationCount_eigen (hκ : 0 < κ) (hε : 0 < ε) (hN : 0 < N)
    (n : ℤ) (m : MArr N) :
    occupationCount L κ ε hκ hε n N (basis hκ hε hN m) = (m.1 n : ℂ) • basis hκ hε hN m := by
  rw [occupationCount,dite_eq_left hN]
  apply diagonal_eigen _ _ (show 0 ≤ (N : ℝ) by positivity) _ m
  intro m
  simpa using (show (m.1 n : ℝ) ≤ N by exact_mod_cast multiplicity_le m n)

theorem positive_sector_bound (hκ : 0 < κ) (hM : 0 < M)
    (hsmall : κ*L*M ≤ 1/1000000) (hN : 0 < N) (hε : 0 < ε)
    (hεM : ε ≤ M) (hbudget : ε*N ≤ M) (n : ℤ) :
    ‖(ε : ℂ) • occupationCount L κ ε hκ hε n N-approximation L κ M ε n N‖ ≤ scalarConstant κ L M*ε^2 ∧
    ‖(ε : ℂ) • occupationCount L κ ε hκ hε n N-hermitianPart (approximation L κ M ε n N)‖ ≤ scalarConstant κ L M*ε^2 := by
  obtain ⟨K,A,hK,hA,_,hn,hh⟩ := actual_diagonal_assembly hκ hM hsmall hN hε hεM hbudget n
  have hk : K = (ε : ℂ) • occupationCount L κ ε hκ hε n N := by
    apply QuantumNLS.NormalityBridge.clm_ext_basis (basis hκ hε hN)
    intro m
    rw [hK m,smul_apply,occupationCount_eigen hκ hε hN,smul_smul]
  have ha : A = approximation L κ M ε n N := by
    apply QuantumNLS.NormalityBridge.clm_ext_basis (basis hκ hε hN)
    intro m
    rw [hA m,approximation_eigen hκ hM hsmall hN hε hεM hbudget]
  simpa only [hk,ha] using And.intro hn hh

/-- The single source theorem, including both literal suprema and every
sector (vacuum included). The constant depends only on L, κ, M. -/
theorem «LOCAL-009» (hκ : 0 < κ) (hM : 0 < M) (hsmall : κ*L*M ≤ 1/1000000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ M →
      (∀ n : ℤ, ∀ N : ℕ, ε*N ≤ M →
        ‖(ε : ℂ) • occupationCount L κ ε hκ hε n N-approximation L κ M ε n N‖ ≤ C*ε^2 ∧
        ‖(ε : ℂ) • occupationCount L κ ε hκ hε n N-hermitianPart (approximation L κ M ε n N)‖ ≤ C*ε^2) ∧
      (⨆ n : ℤ, ⨆ N : {N : ℕ // ε*N ≤ M},
        ‖(ε : ℂ) • occupationCount L κ ε hκ hε n N.1-approximation L κ M ε n N.1‖) ≤ C*ε^2 ∧
      (⨆ n : ℤ, ⨆ N : {N : ℕ // ε*N ≤ M},
        ‖(ε : ℂ) • occupationCount L κ ε hκ hε n N.1-hermitianPart (approximation L κ M ε n N.1)‖) ≤ C*ε^2 := by
  have hC := scalarConstant_nonneg hκ (Fact.out : 0 < L) hM
  refine ⟨scalarConstant κ L M,hC,?_⟩
  intro ε hε hεM
  have all (n : ℤ) (N : ℕ) (hbudget : ε*N ≤ M) :
      ‖(ε : ℂ) • occupationCount L κ ε hκ hε n N-approximation L κ M ε n N‖ ≤ scalarConstant κ L M*ε^2 ∧
      ‖(ε : ℂ) • occupationCount L κ ε hκ hε n N-hermitianPart (approximation L κ M ε n N)‖ ≤ scalarConstant κ L M*ε^2 := by
    by_cases hN : 0 < N
    · exact positive_sector_bound hκ hM hsmall hN hε hεM hbudget n
    · have hzero : N = 0 := by omega
      subst N
      have hk0 : occupationCount L κ ε hκ hε n 0 = 0 := by simp [occupationCount]
      rw [hk0,approximation_vacuum hκ hM hsmall n]
      exact zero_sector_bound ε _ hC
  haveI : Nonempty {N : ℕ // ε*N ≤ M} := ⟨⟨0,by simpa using hM.le⟩⟩
  refine ⟨all,?_,?_⟩
  · exact ciSup_le fun n => ciSup_le fun N => (all n N.1 N.2).1
  · exact ciSup_le fun n => ciSup_le fun N => (all n N.1 N.2).2

end QuantumNLS.LOCAL009R23Final
#print axioms QuantumNLS.LOCAL009R23Final.«LOCAL-009»
