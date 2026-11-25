import QuantumNLS.RadiusBound

/-! integrator-authored trusted spec for DEF-050 "Radius bound for a chosen kernel expansion"
(DEFINITIONS_LEDGER.md:1223; local/quantum_periods.tex:32). Over a complex Hilbert space H, a kernel list
is (A_p)_{0≤p≤N} with A_p a bounded operator on Sym^p H. It is an expansion of the sector operator A_N if
A_N = Σ_p Q_{N,p}(A_p), with Q_{N,p} the realized DEF-009 operator `genericU_N_r` (P_N(A⊗1)P_N). Its radius
bound is Σ_p R^p ‖A_p‖. For R > 0 this is a norm on lists of kernels (zero, triangle inequality,
absolute homogeneity, definiteness); for R ≥ 1 it dominates ‖A_N‖ for every expansion. No uniqueness of
expansions is asserted. -/

open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition

namespace QuantumNLS.DEF050Spec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Literal radius bound Σ_p R^p ‖A_p‖. -/
noncomputable def sRB {N : ℕ} (R : ℝ) (A : (p : Fin (N + 1)) → SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1) : ℝ :=
  ∑ p : Fin (N + 1), R ^ p.1 * ‖A p‖

/-- Literal expansion: A_N = Σ_p Q_{N,p}(A_p) with the realized DEF-009 placement. -/
def sExp {N : ℕ} (AN : SymSector ℂ H N →L[ℂ] SymSector ℂ H N)
    (A : (p : Fin (N + 1)) → SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1) : Prop :=
  AN = ∑ p : Fin (N + 1), genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p)

abbrev KL (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (N : ℕ) :=
  (p : Fin (N + 1)) → SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1

def Spec (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ (N : ℕ),
    (∀ (R : ℝ) (A : KL H N), sRB R A = RadiusBound.radiusBound R A) ∧
    (∀ (AN : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (A : KL H N),
      sExp AN A ↔ RadiusBound.IsExpansion AN A) ∧
    (∀ R : ℝ, 0 < R →
      sRB R (0 : KL H N) = 0 ∧
      (∀ A B : KL H N, sRB R (A + B) ≤ sRB R A + sRB R B) ∧
      (∀ (c : ℂ) (A : KL H N), sRB R (c • A) = ‖c‖ * sRB R A) ∧
      (∀ A : KL H N, sRB R A = 0 ↔ A = 0)) ∧
    (∀ R : ℝ, 1 ≤ R → ∀ (AN : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (A : KL H N),
      sExp AN A → ‖AN‖ ≤ sRB R A)

theorem sExp_iff {N : ℕ} (AN : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) A :
    sExp AN A ↔ RadiusBound.IsExpansion AN A := by
  unfold sExp RadiusBound.IsExpansion RadiusBound.represented
  simp only [RadiusBound.Q_eq_genericU_N_r]

theorem spec : Spec H := by
  intro N
  refine ⟨fun R A => rfl, fun AN A => sExp_iff AN A, fun R hR => ⟨?_, fun A B => ?_, fun c A => ?_,
    fun A => ?_⟩, fun R hR AN A h => ?_⟩
  · exact RadiusBound.radiusBound_zero R
  · exact RadiusBound.radiusBound_add hR.le A B
  · exact RadiusBound.radiusBound_smul R c A
  · exact RadiusBound.radiusBound_eq_zero_iff hR A
  · exact RadiusBound.norm_le_radiusBound hR ((sExp_iff AN A).1 h)

end QuantumNLS.DEF050Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.DEF050Spec.spec
  IO.println s!"DEF050Spec.spec axioms: {ax}"
