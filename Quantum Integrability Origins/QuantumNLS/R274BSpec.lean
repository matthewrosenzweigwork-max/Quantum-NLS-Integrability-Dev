import QuantumNLS.UniformLabelDistance

/-! integrator-authored trusted spec for R-274B2C0D `QG:cor:B3-uniform-label-distance`
(core/QUANTUM_GAUGE_COMPONENTS.tex:99-104, with the chapter convention c = κ/N (line 23) and QG:eq:our-bethe).
An on-shell configuration: N ≥ 1, L, κ > 0, strictly increasing q, nondecreasing integer labels n, and
L q_j = 2π n_j + 2 Σ_{ℓ≠j} arctan(c/(q_j − q_ℓ)) with c = κ/N. Then |q_j − 2πn_j/L| ≤ 3√(κ/L) for all j.
Also for the accepted roots `BetheSmooth.roots L n (κ/N)` with n monotone. -/

namespace QuantumNLS.R274BSpec

def Spec : Prop :=
  (∀ (N : ℕ), 1 ≤ N → ∀ (L κ : ℝ), 0 < L → 0 < κ → ∀ (n : Fin N → ℤ) (q : Fin N → ℝ),
    StrictMono q → Monotone n →
    (∀ j, L * q j = 2 * Real.pi * n j + 2 * ∑ l ∈ Finset.univ.erase j, Real.arctan ((κ / N) / (q j - q l))) →
    ∀ j, |q j - 2 * Real.pi * n j / L| ≤ 3 * Real.sqrt (κ / L)) ∧
  (∀ (N : ℕ), 1 ≤ N → ∀ (L κ : ℝ), 0 < L → 0 < κ → ∀ (n : Fin N → ℤ), Monotone n →
    ∀ j, |BetheSmooth.roots L n (κ / N) j - 2 * Real.pi * n j / L| ≤ 3 * Real.sqrt (κ / L))

theorem spec : Spec := by
  refine ⟨fun N hN L κ hL hκ n q hq hn hE j => ?_, fun N hN L κ hL hκ n hn j =>
    UniformLabelDistance.uniform_label_distance_roots hN hL hκ hn j⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact UniformLabelDistance.uniform_label_distance hN hL hκ
    ⟨div_pos hκ hN0, hq, hn, fun j => hE j⟩ j

end QuantumNLS.R274BSpec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R274BSpec.spec
  IO.println s!"R274BSpec.spec axioms: {ax}"
