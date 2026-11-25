import QuantumNLS.RootDisplacementEstimate

/-! integrator-authored trusted spec for R-B0F552E0 `lem:root-displacement`
(foundations/ROOT_occupation_energy.tex:9). On-shell repulsive configuration with c = κ/N: N ≥ 1, L > 0,
κ > 0, DEF-006 logarithmic labels I (REALIZED: strictly increasing, in ℤ + (N−1)/2), and real q solving
L q_j + 2 Σ_{k≠j} arctan((q_j − q_k)/c) = 2π I_j (written out here). With the DEF-006 corrected
integers n_j (the source's ordered labels; Terra R67: corrected-label interpretation) and p_n = 2πn/L:
(1/N) Σ_j (q_j − p_{n_j})² ≤ (κ/L)(1 − 1/N). -/

open Finset QuantumNLS.BetheLabels

namespace QuantumNLS.RB0F5Spec

def Spec : Prop :=
  ∀ (N : ℕ) (L κ : ℝ), 0 < N → 0 < L → 0 < κ → ∀ (ℓ : LogLabels N) (q : Fin N → ℝ),
    (∀ j : Fin N, L * q j + 2 * ∑ k ∈ univ.erase j, Real.arctan ((q j - q k) / (κ / N)) =
      2 * Real.pi * ℓ.I j) →
    (1 / (N : ℝ)) * ∑ j, (q j - 2 * Real.pi * (correctedInt ℓ j : ℝ) / L) ^ 2 ≤
      (κ / L) * (1 - 1 / (N : ℝ))

theorem spec : Spec := by
  intro N L κ hN hL hκ ℓ q hq
  exact QuantumNLS.RootDisplacementEstimate.root_displacement_estimate ℓ q ⟨hN, hL, hκ, hq⟩

end QuantumNLS.RB0F5Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.RB0F5Spec.spec
  IO.println s!"RB0F5Spec.spec axioms: {ax}"
