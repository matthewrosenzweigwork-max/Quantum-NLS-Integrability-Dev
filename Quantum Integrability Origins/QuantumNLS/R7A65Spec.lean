import QuantumNLS.RootContraction

/-! integrator-authored trusted spec for R-7A6567D6 `F05:root-comparison` (foundations/F05.tex:14).
Two actual repulsive Bethe configurations with the same N, L, c: c > 0, strictly increasing real
rapidities, nondecreasing integer labels, solving eq:root-bose-Bethe
L q_j = 2π n_j + 2 Σ_{k≠j} arctan(c/(q_j − q_k)) (written out here); p_n = 2πn/L. Then
(1/N) Σ |q_j − q̃_j|² ≤ (1/N) Σ |p_{n_j} − p_{ñ_j}|²; if n ≤ ñ componentwise then q ≤ q̃; and
Σ (q̃_j − q_j) = (2π/L) Σ (ñ_j − n_j). -/

open Finset

namespace QuantumNLS.R7A65Spec

def Config (N : ℕ) (L c : ℝ) (n : Fin N → ℤ) (q : Fin N → ℝ) : Prop :=
  0 < c ∧ StrictMono q ∧ Monotone n ∧
  ∀ j, L * q j = 2 * Real.pi * (n j : ℝ) + 2 * ∑ k ∈ univ.erase j, Real.arctan (c / (q j - q k))

def Spec : Prop :=
  ∀ (N : ℕ) (L c : ℝ), 0 < L → ∀ (n nt : Fin N → ℤ) (q qt : Fin N → ℝ),
    Config N L c n q → Config N L c nt qt →
    (1 / (N : ℝ)) * ∑ j, |q j - qt j| ^ 2 ≤
        (1 / (N : ℝ)) * ∑ j, |2 * Real.pi * (n j : ℝ) / L - 2 * Real.pi * (nt j : ℝ) / L| ^ 2 ∧
      ((∀ j, n j ≤ nt j) → ∀ j, q j ≤ qt j) ∧
      ∑ j, (qt j - q j) = 2 * Real.pi / L * ∑ j, ((nt j : ℝ) - n j)

theorem spec : Spec := by
  intro N L c hL n nt q qt ⟨h1, h2, h3, h4⟩ ⟨k1, k2, k3, k4⟩
  exact QuantumNLS.RootContraction.root_comparison hL ⟨h1, h2, h3, h4⟩ ⟨k1, k2, k3, k4⟩

end QuantumNLS.R7A65Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R7A65Spec.spec
  IO.println s!"R7A65Spec.spec axioms: {ax}"
