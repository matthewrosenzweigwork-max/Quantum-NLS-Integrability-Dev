import QuantumNLS.KernelConvergence

/-! integrator-authored trusted spec for DEF-042 "Convergence of the chosen kernel expansions"
(local/quantum_periods.tex:100-110; DEFINITIONS_LEDGER.md:919). For a sequence of chosen expansions
(A_{p,N})_{0≤p≤N} (realized DEF-050 kernel lists; A_{p,N} := 0 for p > N, a convention the source does not
state and which does not affect limits in N) and bounded kernels A_p on Sym^p H: convergence on radius R
means sup_N Σ_p R^p ‖A_{p,N}‖ < ∞ (the realized DEF-050 radius bound) and ‖A_{p,N} − A_p‖ → 0 for each
fixed p. No uniqueness of expansions is assumed. The symbol is a(v) = Σ_p ⟨v^{⊗p}, A_p v^{⊗p}⟩ (realized
DEF-041 tensor power). Proved consequences: Σ_p R^p ‖A_p‖ converges, and for ‖v‖² < R (indeed ≤ R) the symbol
series converges absolutely and is bounded. -/

open Filter Topology
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.LocalPlacement

namespace QuantumNLS.DEF042Spec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def sCoeff (A : ∀ N : ℕ, KernelList (H := H) N) (N p : ℕ) : BoundedSymmetricKernel H p :=
  if h : p ≤ N then A N ⟨p, Nat.lt_succ_of_le h⟩ else 0

def sConv (R : ℝ) (A : ∀ N : ℕ, KernelList (H := H) N) (Alim : ∀ p : ℕ, BoundedSymmetricKernel H p) :
    Prop :=
  (∃ C : ℝ, ∀ N : ℕ, ∑ p : Fin (N + 1), R ^ p.1 * ‖A N p‖ ≤ C) ∧
    ∀ p : ℕ, Tendsto (fun N : ℕ => ‖sCoeff A N p - Alim p‖) atTop (𝓝 0)

/-- Literal symbol term ⟨v^{⊗p}, A_p v^{⊗p}⟩. -/
noncomputable def sTerm {p : ℕ} (A : BoundedSymmetricKernel H p) (v : H) : ℂ :=
  inner ℂ (htpow p v : HilbertTensorPower ℂ H p)
    ((A ⟨htpow p v, htpow_mem_symSector p v⟩ : SymSector ℂ H p) : HilbertTensorPower ℂ H p)

theorem spec :
    (∀ R A Alim, sConv (H := H) R A Alim ↔ KernelConvergence.ConvergesOnRadius R A Alim) ∧
    (∀ (Alim : ∀ p : ℕ, BoundedSymmetricKernel H p) v,
      KernelConvergence.symbol Alim v = ∑' p : ℕ, sTerm (Alim p) v) ∧
    (∀ R : ℝ, 0 ≤ R → ∀ A Alim, sConv (H := H) R A Alim →
      ∃ C : ℝ, Summable (fun p : ℕ => R ^ p * ‖Alim p‖) ∧ (∀ p, R ^ p * ‖Alim p‖ ≤ C) ∧
        ∀ v : H, ‖v‖ ^ 2 ≤ R →
          Summable (fun p : ℕ => ‖sTerm (Alim p) v‖) ∧ ‖∑' p : ℕ, sTerm (Alim p) v‖ ≤ C) ∧
    (∀ R : ℝ, 0 ≤ R → sConv (H := H) R (fun _ => 0) (fun _ => 0)) := by
  have hiff : ∀ R A Alim, sConv (H := H) R A Alim ↔ KernelConvergence.ConvergesOnRadius R A Alim :=
    fun R A Alim => Iff.rfl
  refine ⟨hiff, fun Alim v => rfl, fun R hR A Alim h => ?_, fun R hR =>
    (hiff _ _ _).2 (KernelConvergence.convergesOnRadius_zero R hR)⟩
  obtain ⟨C, h1, -, h3, h4⟩ := KernelConvergence.kernel_convergence hR ((hiff _ _ _).1 h)
  exact ⟨C, h1, h3, h4⟩

end QuantumNLS.DEF042Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.DEF042Spec.spec
  IO.println s!"DEF042Spec.spec axioms: {ax}"
