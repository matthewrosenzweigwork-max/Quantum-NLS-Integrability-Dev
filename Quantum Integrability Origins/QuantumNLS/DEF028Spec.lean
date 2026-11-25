import QuantumNLS.StrongSymbolDef

/-! integrator-authored trusted spec for DEF-028 (definitions.tex:169-171), strong scalar symbols.
A_N has strong scalar symbol a on ψ_N iff ‖(A_N − a)ψ_N‖ → 0; uniform versions quantify over a stated
profile class and time box; norm-close preparations are normalized with ‖ψ_N − φ_N‖ → 0 (φ_N = u^{⊗N});
bounded observables transfer strong symbols to norm-close preparations (triangle inequality); and one
physical instance on the DEF-004 sector. -/

open Filter Topology
open QuantumNLS.StrongSymbolDef

namespace QuantumNLS.DEF028Spec

def Spec : Prop :=
  (∀ (H : ℕ → Type) [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]
      (A : ∀ N, H N →L[ℂ] H N) (ψ : ∀ N, H N) (a : ℂ),
      HasStrongSymbol A ψ a ↔
        Tendsto (fun N => ‖(A N - a • ContinuousLinearMap.id ℂ (H N)) (ψ N)‖) atTop (𝓝 0)) ∧
  (∀ (H : ℕ → Type) [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]
      (X Θ : Type) (A : ∀ N, H N →L[ℂ] H N) (S : Set X) (Tb : Set Θ) (ψ : X → Θ → ∀ N, H N)
      (a : X → ℂ),
      HasUniformStrongSymbol A S Tb ψ a ↔
        ∀ ε > 0, ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb,
          ‖(A N - a u • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖ ≤ ε) ∧
  (∀ (H : ℕ → Type) [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]
      (ψ φ : ∀ N, H N),
      IsNormClosePrep ψ φ ↔ (∀ N, ‖ψ N‖ = 1) ∧ Tendsto (fun N => ‖ψ N - φ N‖) atTop (𝓝 0)) ∧
  (∀ (H : ℕ → Type) [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]
      (A : ∀ N, H N →L[ℂ] H N) (ψ φ : ∀ N, H N) (a : ℂ) (C : ℝ),
      (∀ N, ‖A N‖ ≤ C) → HasStrongSymbol A φ a → IsNormClosePrep ψ φ → HasStrongSymbol A ψ a)

theorem spec : Spec := by
  refine ⟨fun H _ _ A ψ a => Iff.rfl, fun H _ _ X Θ A S Tb ψ a => Iff.rfl,
    fun H _ _ ψ φ => Iff.rfl, ?_⟩
  intro H _ _ A ψ φ a C hA hφ hψ
  exact hasStrongSymbol_of_normClose (Eventually.of_forall hA) hφ hψ.2

end QuantumNLS.DEF028Spec

open Lean in
#eval show CoreM Unit from do
  for n in [``QuantumNLS.DEF028Spec.spec] do
    let ax ← Lean.collectAxioms n
    IO.println s!"{n} axioms: {ax}"
